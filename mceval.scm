;;;; METACIRCULAR EVALUATOR FROM CHAPTER 4 (SECTIONS 4.1.1-4.1.4) of
;;;; STRUCTURE AND INTERPRETATION OF COMPUTER PROGRAMS

;;;; Matches code in ch4.scm, except that "eval" is "mc-eval"
;;;; and "apply" is "mc-apply".

;;;; This file can be loaded into Scheme as a whole.
;;;; Then you can initialize and start the evaluator by evaluating
;;;; the two commented-out lines at the end of the file (setting up the
;;;; global environment and starting the driver loop).
;;;from section 4.1.4 -- must precede def of metacircular apply
#lang r5rs
(#%require (only scheme/base error))
(define apply-in-underlying-scheme apply)

;;;SECTION 4.1.1

(define (mc-eval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp) (lookup-variable-value exp env))
        ((quoted? exp) (text-of-quotation exp))
        ((assignment? exp) (eval-assignment exp env))
        ((definition? exp) (eval-definition exp env))
        ((if? exp) (eval-if exp env))
        ((lambda? exp)
         (make-procedure (lambda-parameters exp)
                         (lambda-body exp)
                         env))
        ((let? exp)
         (mc-eval (let->combination exp) env))
        ((let*? exp)
         (mc-eval (let*->nested-lets exp) env))
        ((unbound? exp) 
         (make-unbound! (cadr exp) env)
         )
        ((begin? exp) 
         (eval-sequence (begin-actions exp) env))
        ((cond? exp) (mc-eval (cond->if exp) env))
        ((application? exp)
         (mc-apply (actual-value (operator exp) env)
                   ;(list-of-values (operands exp) env)
                   (operands exp)
                   env))
         (else
         (error "Unknown expression type -- EVAL" exp))))


(define (mc-apply procedure arguments env)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure (list-of-arg-values arguments env)))
        ((compound-procedure? procedure)
         (eval-sequence
           (procedure-body procedure)
           (extend-environment
             (remove-delay-tag (procedure-parameters procedure))
             (list-of-hybered-args arguments (procedure-parameters procedure) env) ; pass parameters to trace delayed-label
             (procedure-environment procedure))))
        (else
         (error
          "Unknown procedure type -- APPLY" procedure))))


(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (mc-eval (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))

(define (eval-if exp env)
  (if (true? (actual-value (if-predicate exp) env))
      (mc-eval (if-consequent exp) env)
      (mc-eval (if-alternative exp) env)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (actual-value (first-exp exps) env))
        (else (mc-eval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)
                       (mc-eval (assignment-value exp) env)
                       env)
  'ok)

(define (eval-definition exp env)
  (define-variable! (definition-variable exp)
                    (mc-eval (definition-value exp) env)
                    env)
  'ok)

;;;SECTION 4.1.2

(define (self-evaluating? exp)
  (cond ((number? exp) true)
        ((string? exp) true)
        (else false)))

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp) (cadr exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      false))

(define (variable? exp) (symbol? exp))

(define (assignment? exp)
  (tagged-list? exp 'set!))

(define (assignment-variable exp) (cadr exp))

(define (assignment-value exp) (caddr exp))


(define (definition? exp)
  (tagged-list? exp 'define))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp)))
  )

(define (lambda? exp) (tagged-list? exp 'lambda))

(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

(define (if? exp) (tagged-list? exp 'if))

(define (if-predicate exp) (cadr exp))

(define (if-consequent exp) (caddr exp))

(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))


(define (begin? exp) (tagged-list? exp 'begin))

(define (begin-actions exp) (cdr exp))

(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons 'begin seq))


(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))


(define (cond? exp) (tagged-list? exp 'cond))

(define (cond-clauses exp) (cdr exp))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define (cond-predicate clause) (car clause))

(define (cond-actions clause) (cdr clause))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
      'false                          ; no else clause
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't last -- COND->IF"
                       clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))

;;;SECTION 4.1.3

(define (true? x)
  (not (eq? x false)))

(define (false? x)
  (eq? x false))


(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (compound-procedure? p)
  (tagged-list? p 'procedure))


(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))


(define (enclosing-environment env) (cdr env))

(define (first-frame env) (car env))

(define the-empty-environment '())

(define (make-frame variables values)
  (cons variables values))

(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))

(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))

(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied" vars vals)
          (error "Too few arguments supplied" vars vals))))

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (car vals))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET!" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars)
             (add-binding-to-frame! var val frame))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))

;;;SECTION 4.1.4

(define (setup-environment)
  (let ((initial-env
         (extend-environment (primitive-procedure-names)
                             (primitive-procedure-objects)
                             the-empty-environment)))
    (define-variable! 'true true initial-env)
    (define-variable! 'false false initial-env)
    initial-env))

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc) (cadr proc))

(define true #t)
(define false #f)
(define (1+ x) (+ 1 x))
(define (-1+ x) (- x 1))

(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cons cons)
        (list 'null? null?)
        (list 'zero? zero?)
        (list 'eq? eq?)
        (list 'equal? equal?)
        (list '1+ 1+)
        (list '-1+ -1+)
        (list 'quotient quotient)
        (list 'remainder remainder)
        (list '/ /)
        (list '* *)
        (list '+ +)
        (list '- -)
        (list '= =)
        ))

(define (primitive-procedure-names)
  (map car
       primitive-procedures))

(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc)))
       primitive-procedures))


(define (apply-primitive-procedure proc args)
  (apply-in-underlying-scheme
   (primitive-implementation proc) args))

(define input-prompt ";;; M-Eval input:")
(define output-prompt ";;; M-Eval value:")

(define (driver-loop)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    ;(display (exp-list input))
    (let ((output (actual-value input the-global-environment)))
      (announce-output output-prompt)
      (user-print output)))
  (driver-loop))

(define (prompt-for-input string)
  (newline) (newline) (display string) (newline))


(define (announce-output string)
  (newline) (display string) (newline))

(define (user-print object)
  (if (compound-procedure? object)
      (display (list 'compound-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))
;;==================================Exercise 4.6============================================

(define (let? exp) (tagged-list? exp 'let )); check tag
(define (let-var-exps exp) (car (cdr exp))) ; get the var-exp pairs
(define (let-body exp) (cddr exp)) ;get the body 
(define (let-var var-exp) (car var-exp)) ;for every (<var, exp>), get the var
(define (let-exp var-exp) (car (cdr var-exp))) ;for every (<var,exp>), get the exp

(define (var-list exp) (map (lambda (x) (let-var x)) (let-var-exps exp)));get the var out of the var-exp list
(define (exp-list exp) (map (lambda (x) (let-exp x)) (let-var-exps exp)));get the exp out of the var-exp list

(define (let->combination exp)   ; chain lambda with the expressions
  (cons (list 'begin (make-lambda 
                          (var-list exp) 
                          (let-body exp))) 
             (exp-list exp))
)



;;==================================Exercise 4.7============================================

(define (let*? exp) (tagged-list? exp 'let*))
(define (extend-let* var-exp-pairs body)
  (if (null? (cdr var-exp-pairs))  
      (cons 'let (cons var-exp-pairs body)) ;if var-exp-pairs contain only 1 pair then deal with body
      (list 'let (list (car var-exp-pairs)) 
            (extend-let* (cdr var-exp-pairs) body)) ;chain the var-exp-pair to let
      )
  )
(define (let*->nested-lets exp)
  (extend-let* (let-var-exps exp) (let-body exp))
  )

;;==================================Exercise 4.13============================================

(define (make-unbound! var env)
  (let ((frame (first-frame env)));get current frame
    (define (scan vars vals)
      (cond ((null? vars)
             (error "Unbound variable -- MAKE-UNBOUND!" var));not find the var, already unbinded
            ((eq? var (car vars)) ;find the var
             (set-car! vars '()) ; set to empty
             (set-car! vals '())); set to empty
            (else (scan (cdr vars) (cdr vals))))) ;keep scanning
    (scan (frame-variables frame)
          (frame-values frame))))
(define (unbound? exp) (tagged-list? exp 'unbound ))






;;==================================Problem 1=================================================
(define (actual-value exp env)
  (force-it (mc-eval exp env)))

(define (force-it obj)
  (if (thunk? obj)
      (actual-value (thunk-exp obj) (thunk-env obj))
      obj))
(define (delay-it exp env)
  (list 'thunk exp env))
(define (thunk? obj)
  (tagged-list? obj 'thunk))
(define (thunk-exp thunk) (cadr thunk))
(define (thunk-env thunk) (caddr thunk))

(define (list-of-arg-values exps env)
  (if (no-operands? exps)
      '()
      (cons (actual-value (first-operand exps) env) ; if have delayed sign?
            (list-of-arg-values (rest-operands exps)
                                env))))




(define (check-delay parameter) 
  (cond ((pair? parameter)
         (cond ((eq? (car parameter) 'delayed) true)
               (else false))
         )
        (else false)
        )
  )
(define (first-parameter parameters) (car parameters))
(define (rest-parameter parameters) (cdr parameters))
(define (list-of-hybered-args exps parameters env)
  (if (no-operands? exps)
      '()
      (cond  ((check-delay (first-parameter parameters))  ;if it is labeled as delayed
             (cons (delay-it (first-operand exps) env) ;get the exps, abandon the label
                    (list-of-hybered-args (rest-operands exps) (rest-parameter parameters)
                                  env)))         
            (else 
             (cons (actual-value (first-operand exps) env) ;if not labeled as delayed, then force it
                  (list-of-hybered-args (rest-operands exps) (rest-parameter parameters)
                                      env))
            ))))
      

(define (remove-delay-tag parameters)
  (if (null? parameters)
      '()
      (if (pair? (first-parameter parameters))
          (if (eq? (car (first-parameter parameters)) 'delayed)
              (cons (cadr (first-parameter parameters)) (remove-delay-tag (rest-parameter parameters)))
              (error "Not an identifier in: Remove-delay-tag")
              )
          (cons (first-parameter parameters) (remove-delay-tag (rest-parameter parameters)))
          )
      )
  )
      
      
      
      
      
      
      
      













(define the-global-environment (setup-environment))

(list "To start the metacircular evaluator, evaluate (driver-loop)")

'METACIRCULAR-EVALUATOR-LOADED
(driver-loop)