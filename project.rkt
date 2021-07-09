;; PL Project - Fall 2020
;; NUMEX interpreter

#lang racket
(provide (all-defined-out))

;; definition of structures for NUMEX programs

(struct var  (s) #:transparent)  ;; a variable, e.g., (var "foo")
(struct num  (n) #:transparent)  ;; a constant number, e.g., (num 17)
(struct bool (b) #:transparent)  ;; a boolean, which is either #t or #f

(struct plus  (e1 e2) #:transparent)  ;; add two expressions
(struct minus (e1 e2) #:transparent)  ;; subtract two expressions
(struct mult  (e1 e2) #:transparent)  ;; multiply two expressions
(struct div   (e1 e2) #:transparent)  ;; divide two expressions
(struct neg   (e1)    #:transparent)  ;; negate an expression

(struct andalso (e1 e2)       #:transparent)  ;; logical conjunction
(struct orelse  (e1 e2)       #:transparent)  ;; logical disjunction
(struct cnd     (e1 e2 e3)    #:transparent)  ;; general if-then-else condition
(struct iseq    (e1 e2)       #:transparent)  ;; comparison
(struct ifnzero (e1 e2 e3)    #:transparent)  ;; if e1 is not zero then e2, else e3
(struct ifleq   (e1 e2 e3 e4) #:transparent)  ;; if e1 <= e2 then e3, else e4

(struct lam   (s1 s2 e) #:transparent)  ;; a recursive(?) 1-argument function
(struct apply (e1 e2)   #:transparent)  ;; function application
(struct with  (s e1 e2) #:transparent)  ;; variable assignment

(struct apair (e1 e2) #:transparent)  ;; pair constructor
(struct 1st   (e1)    #:transparent)  ;; the first part of a pair
(struct 2nd   (e1)    #:transparent)  ;; the second part of a pair

(struct munit   ()   #:transparent)  ;; unit value -- good for ending a list
(struct ismunit (e1) #:transparent)  ;; if e1 is unit then true else false

(struct closure (env f)  #:transparent)  ;; a closure is not in "source" programs; it is what functions evaluate to

(struct letrec (s1 e1 s2 e2 s3 e3 s4 e4 e5) #:transparent)  ;; a letrec expression for recursive definitions

(struct key    (s e) #:transparent)  ;; key holds corresponding value of s which is e
(struct record (k r) #:transparent)  ;; record holds several keys
(struct value  (s r) #:transparent)  ;; value returns corresponding value of s in r


;; XOR:
(struct xor (e1 e2) #:transparent)


;; -----------------------------------------------------------------------------------------------------------------------------------------------------------
;; Problem 1

(define (racketlist->numexlist xs)  ;; e.g. (racketlist->numexlist '("a" "b" "c")) 
  (cond ((list? xs) (cond ((null? xs) (munit))
                          (else (apair (car xs) (racketlist->numexlist (cdr xs))))))
        (else (error (format "~v is not a Racket list." xs)))))

(define (numexlist->racketlist xs)  ; e.g. (numexlist->racketlist (apair "a" (apair "b" (apair "c" (munit)))))
  (cond ((munit? xs) null)
        (else (cons (apair-e1 xs) (numexlist->racketlist (apair-e2 xs))))))


;; -----------------------------------------------------------------------------------------------------------------------------------------------------------
;; Problem 2

;; lookup a variable in an environment
;; e.g. (envlookup '(("a" . (num 1)) ("c" . (num 2))) "c")
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
  		[else (cond ((eq? (car (car env)) str) (cdr (car env)))
                          (else (envlookup (cdr env) str)))]
		)
)

;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  (cond [(var? e) 
         (envlookup env (var-s e))]

        [(num? e)
         (cond ((integer? (num-n e)) e)
               (else (error (format "~v is not an integer value." (num-n e)))))]
        
        [(bool? e)
         (cond ((boolean? (bool-b e)) e)
               (else (error (format "~v is not a boolean value." (bool-b e)))))]
        
        [(munit? e) e]
        
        [(closure? e) e]

        [(plus? e)  ;; e.g. (eval-exp (plus (num 1) (num 2)))
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
           (if (and (num? v1) (num? v2))
               (num (+ (num-n v1) (num-n v2)))
               (error "NUMEX addition applied to non-number.")))]

        [(minus? e)  ;; e.g. (eval-exp (minus (num 5) (num 3)))
         (let ([v1 (eval-under-env (minus-e1 e) env)]
               [v2 (eval-under-env (minus-e2 e) env)])
           (if (and (num? v1) (num? v2))
               (num (- (num-n v1) (num-n v2)))
               (error "NUMEX subtraction applied to non-number.")))]

        [(mult? e)  ;; e.g. (eval-exp (mult (num 4) (num 3)))
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (num? v1) (num? v2))
               (num (* (num-n v1) (num-n v2)))
               (error "NUMEX multiplication applied to non-number.")))]

        [(div? e)  ;; e.g. (eval-exp (div (num 4) (num 3)))
         (let ([v1 (eval-under-env (div-e1 e) env)]
               [v2 (eval-under-env (div-e2 e) env)])
           (if (and (num? v1) (num? v2))
               (num (quotient (num-n v1) (num-n v2)))
               (error "NUMEX division applied to non-number.")))]

        [(neg? e)  ;; e.g. (eval-exp (neg (num 3))), (eval-exp (neg (bool #t)))
         (let ([v (eval-under-env (neg-e1 e) env)])
           (cond ((num? v) (num (- (num-n v))))
                 ((bool? v) (bool (not (bool-b v))))
                 (else (error "expression does not evaluate to a number or a boolean."))))]

        [(andalso? e) ;; e.g. (eval-exp (andalso (bool #t) (bool #f)))
         (let ([v (eval-under-env (andalso-e1 e) env)])
           (cond ((bool-b v) (eval-under-env (andalso-e2 e) env))
                 (else (bool #f))))]

        [(orelse? e) ;; e.g. (eval-exp (orelse (bool #t) (bool #f)))
         (let ([v (eval-under-env (orelse-e1 e) env)])
           (cond ((bool-b v) (bool #t))
                 (else (eval-under-env (orelse-e2 e) env))))]

        [(cnd? e)  ;; e.g. (eval-exp (cnd (bool #t) (num 1) (num 2)))
         (let ([v (eval-under-env (cnd-e1 e) env)])
           (cond ((bool? v) (cond ((bool-b v) (eval-under-env (cnd-e2 e) env))
                 (else (eval-under-env (cnd-e3 e) env))))
                 (else (error "condition doesn't evaluate to a bool."))))]

        [(iseq? e)  ;; e.g. (eval-exp (iseq (num 3) (plus (num 2) (num 1))))
         (let ([v1 (eval-under-env (iseq-e1 e) env)]
               [v2 (eval-under-env (iseq-e2 e) env)])
           (bool (equal? v1 v2)))]

        [(ifnzero? e)  ;; e.g. (eval-exp (ifnzero (num 1) (num 2) (num 3)))
         (let ([v (eval-under-env (ifnzero-e1 e) env)])
           (cond ((num? v) (eval-under-env (cnd (eval-under-env (iseq v (num 0)) env) (ifnzero-e3 e) (ifnzero-e2 e)) env))
                 (else (error (format "~v is not a number." v)))))]

        [(ifleq? e)  ;; e.g. (eval-exp (ifleq (num 4) (num 3) (num 10) (num 20)))
         (let ([v1 (eval-under-env (ifleq-e1 e) env)]
               [v2 (eval-under-env (ifleq-e2 e) env)])
           (cond ((and (num? v1) (num? v2)) (cond ((> (num-n v1) (num-n v2)) (eval-under-env (ifleq-e4 e) env))
               (else (eval-under-env (ifleq-e3 e) env))))
                 (else (error "e1 and e2 must evaluate to numbers."))))]

        [(with? e) ;; e.g. (eval-exp (with "a" (plus (num 1) (num 2)) (mult (var "a") (var "a"))))
         (eval-under-env (with-e2 e) (cons (cons (with-s e) (eval-under-env (with-e1 e) env)) env))]

        ;; NOTICE: when a function is evaluated, it gets a copy of the environment at that moment, and it won't be updated afterwards.
        ;; (except for the local variables in the function). So be careful when you evaluate it!
        [(lam? e) (closure env e)]

        ;; e.g. successor: (eval-exp (apply (lam null "n" (plus (var "n") (num 1))) (num 3)))
        ;; e.g. recursive factorial: (eval-exp (apply (lam "fact" "n" (ifnzero (var "n") (mult (var "n") (apply (var "fact") (minus (var "n") (num 1)))) (num 1))) (num 4)))
        [(apply? e) 
         (let ([c (eval-under-env (eval-under-env (apply-e1 e) env) env)])
           (cond ((closure? c) (eval-under-env (lam-e (closure-f c))
                                               (cond ((null? (lam-s1 (closure-f c))) (cons (cons (lam-s2 (closure-f c)) (eval-under-env (apply-e2 e) env)) (closure-env c)))
                                                     (else (cons (cons (lam-s1 (closure-f c)) c) (cons (cons (lam-s2 (closure-f c)) (eval-under-env (apply-e2 e) env)) (closure-env c)))))))
                 (else (error (format "~v is not a function" c)))))]

        [(apair? e) ;; (eval-exp (apair (plus (num 4) (num 2)) (andalso (bool #t) (bool #f))))
         (apair (eval-under-env (apair-e1 e) env) (eval-under-env (apair-e2 e) env))]

        [(1st? e)  ;; (eval-exp (1st (apair (plus (num 4) (num 2)) (andalso (bool #t) (bool #f)))))
         (let ([v (eval-under-env (1st-e1 e) env)])
           (cond ((apair? v)(apair-e1 v))
                 (else (error "input doesn't evaluate to a pair"))))]
        
        [(2nd? e)  ;; (eval-exp (2nd (apair (plus (num 4) (num 2)) (andalso (bool #t) (bool #f)))))
         (let ([v (eval-under-env (2nd-e1 e) env)])
           (cond ((apair? v)(apair-e2 v))
                 (else (error "input doesn't evaluate to a pair"))))]

        [(ismunit? e)  ;; (eval-exp (ismunit (munit)))
         (cond ((munit? (eval-under-env (ismunit-e1 e) env))(bool #t))
               (else (bool #f)))]

        ;; NOTICE: In this NUMEX expression, the lam itself is put into the environment, not the closure. i.e. the function is not evaluated.
        ;; Therefore, (eval-exp (var "f")) would give us a lam, which must be evaluated one more time to give us a closure. That's the reason
        ;; we have two nested eval-exps in the semanticts of apply expression.
        [(letrec? e)
         (eval-under-env (letrec-e5 e)
                         (cons (cons (letrec-s1 e) (letrec-e1 e))
                         (cons (cons (letrec-s2 e) (letrec-e2 e))
                         (cons (cons (letrec-s3 e) (letrec-e3 e))
                         (cons (cons (letrec-s4 e) (letrec-e4 e)) env)))))]

        [(key? e) ;; (eval-exp (key "a" (plus (num 1) (num 2))))
         (key (key-s e) (eval-under-env (key-e e) env))]

        [(record? e)  ;; (eval-exp (record (key "b" (num 2)) (record (key "a" (num 1)) (munit))))
         (let ([v1 (eval-under-env (record-k e) env)]
               [v2 (eval-under-env (record-r e) env)])
           (cond ((key? v1) (cond ((or (munit? v2) (record? v2)) (record v1 v2))
                                  (else (error "the second argument is neither munit nor record"))))
                 (else (error "the frist argument is not a key"))))]


        [(value? e)
         (let ([r (eval-under-env (value-r e) env)])
           (cond ((record? r) (cond ((eq? (key-s (record-k r)) (value-s e)) (key-e (record-k r)))
                                    (else (cond ((record? (record-r r)) (eval-under-env (value (value-s e) (record-r r)) env))
                                                (else (munit))))))
                 (else (error "the second argument isn't a record."))))]

        ;; XOR
        ;; e.g. (eval-exp (xor (bool #t) (bool #f)))
        [(xor? e)
         (let ([v1 (eval-under-env (xor-e1 e) env)]
               [v2 (eval-under-env (xor-e2 e) env)])
           (cond ((or (bool? v1) (bool? v2))
                  (cond ((equal? v1 v2) (bool #f))
                        (else (bool #t))))
                 (else (error "wrong types!"))))]

        
        [else (error (format "bad NUMEX expression: ~v" e))]))


;; -----------------------------------------------------------------------------------------------------------------------------------------------------------
;; Problem 3

(define (ifmunit e1 e2 e3)  ;; e.g. (ifmunit (munit) (plus (num 1) (num 2)) (plus (num 3) (num 4)))
  (cnd (ismunit e1) e2 e3))

(define (with* bs e2)  ;; e.g. (with* '(("a" . (num 3)) ("b" . (plus (var "a") (num 1)))) (mult (var "a") (var "b")))
  (cond ((null? bs) e2)
        (else (with (car (car bs)) (cdr (car bs)) (with* (cdr bs) e2)))))

(define (ifneq e1 e2 e3 e4)  ;; e.g. (ifneq (num 1) (num 2) (mult (num 2) (num 2)) (mult (num 3) (num 3)))
  (cnd (iseq e1 e2) e4 e3))


;; -----------------------------------------------------------------------------------------------------------------------------------------------------------
;; Problem 4

(define numex-filter  ;; e.g (eval-exp (apply (apply numex-filter (lam null "x" (minus (var "x") (num 1)))) (apair (num 1) (apair (num 2) (munit)))))
  (lam null "f" (lam "map" "l" (cnd (ismunit (var "l")) (munit)
                                    (with "v" (apply (var "f") (1st (var "l"))) (ifnzero (var "v") (apair (var "v") (apply (var "map") (2nd (var "l"))))
                                                                                      (apply (var "map") (2nd (var "l")))))))))

(define numex-all-gt  ;; e.g. (eval-exp (apply (apply numex-all-gt (num 5)) (apair (num 5) (apair (num 6) (munit)))))
  (with "filter" numex-filter
        (lam null "i" (apply (var "filter") (lam null "x" (ifleq (var "x") (var "i") (num 0) (var "x")))))))


;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))


;; -----------------------------------------------------------------------------------------------------------------------------------------------------------
;; Challenge Problem

(struct fun-challenge (s1 s2 e freevars) #:transparent) ;; a recursive(?) 1-argument function


;; We will test this function directly, so it must do as described in the assignment
(define (compute-free-vars e)
  (car (fixed-expr-and-freevars e)))


;; this function ran on any expression, gives us a cons with the first part
;; holding the fixed expression (all 'lam's converted to 'fun-challenge') and
;; the second part holding the set of free variables in that expression.
(define (fixed-expr-and-freevars e)
  (cond [(var? e)  ;; e.g. (fixed-expr-and-freevars (var "a"))
         (cons e (set (var-s e)))]

        [(num? e)
         (cons e (set))]

        [(bool? e)
         (cons e (set))]

        [(munit? e)
         (cons e (set))]

        [(closure? e)
         (cons e (set))]

        [(plus? e)  ;; e.g. (fixed-expr-and-freevars (plus (var "a") (var "b")))
         (let ([v1 (fixed-expr-and-freevars (plus-e1 e))]
               [v2 (fixed-expr-and-freevars (plus-e2 e))])
           (cons (plus (car v1) (car v2))
                 (set-union (cdr v1) (cdr v2))))]

        [(minus? e)
         (let ([v1 (fixed-expr-and-freevars (minus-e1 e))]
               [v2 (fixed-expr-and-freevars (minus-e2 e))])
           (cons (minus (car v1) (car v2))
                 (set-union (cdr v1) (cdr v2))))]
        
        [(mult? e)
         (let ([v1 (fixed-expr-and-freevars (mult-e1 e))]
               [v2 (fixed-expr-and-freevars (mult-e2 e))])
           (cons (mult (car v1) (car v2))
                 (set-union (cdr v1) (cdr v2))))]

        [(div? e)
         (let ([v1 (fixed-expr-and-freevars (div-e1 e))]
               [v2 (fixed-expr-and-freevars (div-e2 e))])
           (cons (div (car v1) (car v2))
                 (set-union (cdr v1) (cdr v2))))]

        [(neg? e)  ;; e.g. (fixed-expr-and-freevars (neg (var "a")))
         (let ([v (fixed-expr-and-freevars (neg-e1 e))])
           (cons (neg (car v)) (cdr v)))]

        [(andalso? e)
         (let ([v1 (fixed-expr-and-freevars (andalso-e1 e))]
               [v2 (fixed-expr-and-freevars (andalso-e2 e))])
           (cons (andalso (car v1) (car v2))
                 (set-union (cdr v1) (cdr v2))))]

        [(orelse? e)
         (let ([v1 (fixed-expr-and-freevars (orelse-e1 e))]
               [v2 (fixed-expr-and-freevars (orelse-e2 e))])
           (cons (orelse (car v1) (car v2))
                 (set-union (cdr v1) (cdr v2))))]

        [(cnd? e)
         (let ([v1 (fixed-expr-and-freevars (cnd-e1 e))]
               [v2 (fixed-expr-and-freevars (cnd-e2 e))]
               [v3 (fixed-expr-and-freevars (cnd-e3 e))])
           (cons (cnd (car v1) (car v2) (car v3))
                 (set-union (cdr v1) (cdr v2) (cdr v3))))]

        [(iseq? e)
         (let ([v1 (fixed-expr-and-freevars (iseq-e1 e))]
               [v2 (fixed-expr-and-freevars (iseq-e2 e))])
           (cons (iseq (car v1) (car v2))
                 (set-union (cdr v1) (cdr v2))))]

        [(ifnzero? e)
         (let ([v1 (fixed-expr-and-freevars (ifnzero-e1 e))]
               [v2 (fixed-expr-and-freevars (ifnzero-e2 e))]
               [v3 (fixed-expr-and-freevars (ifnzero-e3 e))])
           (cons (ifnzero (car v1) (car v2) (car v3))
                 (set-union (cdr v1) (cdr v2) (cdr v3))))]

        [(ifleq? e)
         (let ([v1 (fixed-expr-and-freevars (ifleq-e1 e))]
               [v2 (fixed-expr-and-freevars (ifleq-e2 e))]
               [v3 (fixed-expr-and-freevars (ifleq-e3 e))]
               [v4 (fixed-expr-and-freevars (ifleq-e4 e))])
           (cons (ifleq (car v1) (car v2) (car v3) (car v4))
                 (set-union (cdr v1) (cdr v2) (cdr v3) (cdr v4))))]

        [(with? e)  ;; e.g. (fixed-expr-and-freevars (with "a" (var "b") (plus (var "a") (num 1))))
         (let ([v1 (fixed-expr-and-freevars (with-e1 e))]
               [v2 (fixed-expr-and-freevars (with-e2 e))])
           (cons (with (with-s e) (car v1) (car v2))
                 (set-remove (set-union (cdr v1) (cdr v2)) (with-s e))))]

        ;; e.g. (fixed-expr-and-freevars (lam null "n" (plus (var "n") (num 1))))
        [(lam? e)
         (let ([v (fixed-expr-and-freevars (lam-e e))])
           (let ([vars (set-remove (set-remove (cdr v) (lam-s1 e)) (lam-s2 e))])
             (cons (fun-challenge (lam-s1 e) (lam-s2 e) (car v) vars) vars)))]

        ;; e.g. (fixed-expr-and-freevars (lam "fact" "n" (ifnzero (var "n") (mult (var "n") (apply (var "fact") (minus (var "n") (num 1)))) (num 1))))
        [(apply? e)
         (let ([v1 (fixed-expr-and-freevars (apply-e1 e))]
               [v2 (fixed-expr-and-freevars (apply-e2 e))])
           (cons (apply (car v1) (car v2))
                 (set-union (cdr v1) (cdr v2))))]

        [(apair? e)
         (let ([v1 (fixed-expr-and-freevars (apair-e1 e))]
               [v2 (fixed-expr-and-freevars (apair-e2 e))])
           (cons (apair (car v1) (car v2))
                 (set-union (cdr v1) (cdr v2))))]

        [(1st? e)
         (let ([v (fixed-expr-and-freevars (1st-e1 e))])
           (cons (1st (car v))
                 (cdr v)))]

        [(2nd? e)
         (let ([v (fixed-expr-and-freevars (2nd-e1 e))])
           (cons (2nd (car v))
                 (cdr v)))]

        [(ismunit? e)
         (let ([v (fixed-expr-and-freevars (ismunit-e1 e))])
           (cons (ismunit (car v))
                 (cdr v)))]

        [(letrec? e)
         (let ([v1 (fixed-expr-and-freevars (letrec-e1 e))]
               [v2 (fixed-expr-and-freevars (letrec-e2 e))]
               [v3 (fixed-expr-and-freevars (letrec-e3 e))]
               [v4 (fixed-expr-and-freevars (letrec-e4 e))]
               [v5 (fixed-expr-and-freevars (letrec-e5 e))])
           (cons (letrec (letrec-s1 e) (car v1) (letrec-s2 e) (car v2) (letrec-s3 e) (car v3)(letrec-s4 e) (car v4) (car v5))
                 (set-remove (set-remove (set-remove (set-remove
                                                      (set-union (cdr v1) (cdr v2) (cdr v3) (cdr v4) (cdr v5))(letrec-s1 e)) (letrec-s2 e)) (letrec-s3 e)) (letrec-s3 e))))]

        [(key? e)
         (let ([v (fixed-expr-and-freevars (key-e e))])
           (cons (key (key-s e) (car v))
                 (cdr v)))]
        
        [(record? e)
         (let ([v1 (fixed-expr-and-freevars (record-k e))]
               [v2 (fixed-expr-and-freevars (record-r e))])
           (cons (record (car v1) (car v2))
                 (set-union (cdr v1) (cdr v2))))]

        [(value? e)
         (let ([v (fixed-expr-and-freevars (value-r))])
           (cons (value (value-s e) (car v))
                 (cdr v)))]
        
         [else (error (format "bad NUMEX expression: ~v " e))]))

        
;; -----------------------------------------------------------------------------------------------------------------------------------------------------------
;; This function returns a subset of the env which only contains the variables in freevars
(define (get-sub-env env freevars)  ;; e.g. (get-sub-env '(("a" . (num 1)) ("c" . (num 2))) (set "a"))
  (cond ((null? env) null)
        (else (cond ((set-member? freevars (car (car env))) (cons (car env) (get-sub-env (cdr env) freevars)))
                    (else (get-sub-env (cdr env) freevars))))))


;; Do NOT share code with eval-under-env because that will make grading
;; more difficult, so copy most of your interpreter here and make minor changes
;; The only difference between this and eval-under-env is having fun-challenge instead of lam
(define (eval-under-env-c e env)
  (cond [(var? e) 
         (envlookup env (var-s e))]

        [(num? e)
         (cond ((integer? (num-n e)) e)
               (else (error (format "~v is not an integer value." (num-n e)))))]
        
        [(bool? e)
         (cond ((boolean? (bool-b e)) e)
               (else (error (format "~v is not a boolean value." (bool-b e)))))]
        
        [(munit? e) e]
        
        [(closure? e) e]

        [(plus? e)  ;; e.g. (eval-exp (plus (num 1) (num 2)))
         (let ([v1 (eval-under-env-c (plus-e1 e) env)]
               [v2 (eval-under-env-c (plus-e2 e) env)])
           (if (and (num? v1) (num? v2))
               (num (+ (num-n v1) (num-n v2)))
               (error "NUMEX addition applied to non-number.")))]

        [(minus? e)  ;; e.g. (eval-exp (minus (num 5) (num 3)))
         (let ([v1 (eval-under-env-c (minus-e1 e) env)]
               [v2 (eval-under-env-c (minus-e2 e) env)])
           (if (and (num? v1) (num? v2))
               (num (- (num-n v1) (num-n v2)))
               (error "NUMEX subtraction applied to non-number.")))]

        [(mult? e)  ;; e.g. (eval-exp (mult (num 4) (num 3)))
         (let ([v1 (eval-under-env-c (mult-e1 e) env)]
               [v2 (eval-under-env-c (mult-e2 e) env)])
           (if (and (num? v1) (num? v2))
               (num (* (num-n v1) (num-n v2)))
               (error "NUMEX multiplication applied to non-number.")))]

        [(div? e)  ;; e.g. (eval-exp (div (num 4) (num 3)))
         (let ([v1 (eval-under-env-c (div-e1 e) env)]
               [v2 (eval-under-env-c (div-e2 e) env)])
           (if (and (num? v1) (num? v2))
               (num (quotient (num-n v1) (num-n v2)))
               (error "NUMEX division applied to non-number.")))]

        [(neg? e)  ;; e.g. (eval-exp (neg (num 3))), (eval-exp (neg (bool #t)))
         (let ([v (eval-under-env-c (neg-e1 e) env)])
           (cond ((num? v) (num (- (num-n v))))
                 ((bool? v) (bool (not (bool-b v))))
                 (else (error "expression does not evaluate to a number or a boolean."))))]

        [(andalso? e) ;; e.g. (eval-exp (andalso (bool #t) (bool #f)))
         (let ([v (eval-under-env-c (andalso-e1 e) env)])
           (cond ((bool-b v) (eval-under-env-c (andalso-e2 e) env))
                 (else (bool #f))))]

        [(orelse? e) ;; e.g. (eval-exp (orelse (bool #t) (bool #f)))
         (let ([v (eval-under-env-c (orelse-e1 e) env)])
           (cond ((bool-b v) (bool #t))
                 (else (eval-under-env-c (orelse-e2 e) env))))]

        [(cnd? e)  ;; e.g. (eval-exp (cnd (bool #t) (num 1) (num 2)))
         (let ([v (eval-under-env-c (cnd-e1 e) env)])
           (cond ((bool? v) (cond ((bool-b v) (eval-under-env-c (cnd-e2 e) env))
                 (else (eval-under-env-c (cnd-e3 e) env))))
                 (else (error "condition doesn't evaluate to a bool."))))]

        [(iseq? e)  ;; e.g. (eval-exp (iseq (num 3) (plus (num 2) (num 1))))
         (let ([v1 (eval-under-env-c (iseq-e1 e) env)]
               [v2 (eval-under-env-c (iseq-e2 e) env)])
           (bool (equal? v1 v2)))]

        [(ifnzero? e)  ;; e.g. (eval-exp (ifnzero (num 1) (num 2) (num 3)))
         (let ([v (eval-under-env-c (ifnzero-e1 e) env)])
           (cond ((num? v) (eval-under-env-c (cnd (eval-under-env-c (iseq v (num 0)) env) (ifnzero-e3 e) (ifnzero-e2 e)) env))
                 (else (error (format "~v is not a number." v)))))]

        [(ifleq? e)  ;; e.g. (eval-exp (ifleq (num 4) (num 3) (num 10) (num 20)))
         (let ([v1 (eval-under-env-c (ifleq-e1 e) env)]
               [v2 (eval-under-env-c (ifleq-e2 e) env)])
           (cond ((and (num? v1) (num? v2)) (cond ((> (num-n v1) (num-n v2)) (eval-under-env-c (ifleq-e4 e) env))
               (else (eval-under-env-c (ifleq-e3 e) env))))
                 (else (error "e1 and e2 must evaluate to numbers."))))]

        [(with? e) ;; e.g. (eval-exp (with "a" (plus (num 1) (num 2)) (mult (var "a") (var "a"))))
         (eval-under-env-c (with-e2 e) (cons (cons (with-s e) (eval-under-env-c (with-e1 e) env)) env))]

        ;; We have this guy instead of lam
        [(fun-challenge? e)
         (closure (get-sub-env env (fun-challenge-freevars e)) (lam (fun-challenge-s1 e) (fun-challenge-s2 e) (fun-challenge-e e)))]

        ;; e.g. successor: (eval-exp (apply (lam null "n" (plus (var "n") (num 1))) (num 3)))
        ;; e.g. recursive factorial: (eval-exp (apply (lam "fact" "n" (ifnzero (var "n") (mult (var "n") (apply (var "fact") (minus (var "n") (num 1)))) (num 1))) (num 4)))
        [(apply? e) 
         (let ([c (eval-under-env-c (eval-under-env-c (apply-e1 e) env) env)])
           (cond ((closure? c) (eval-under-env-c (lam-e (closure-f c))
                                               (cond ((null? (lam-s1 (closure-f c))) (cons (cons (lam-s2 (closure-f c)) (eval-under-env-c (apply-e2 e) env)) (closure-env c)))
                                                     (else (cons (cons (lam-s1 (closure-f c)) c) (cons (cons (lam-s2 (closure-f c)) (eval-under-env-c (apply-e2 e) env)) (closure-env c)))))))
                 (else (error (format "~v is not a function" c)))))]

        [(apair? e) ;; (eval-exp (apair (plus (num 4) (num 2)) (andalso (bool #t) (bool #f))))
         (apair (eval-under-env-c (apair-e1 e) env) (eval-under-env-c (apair-e2 e) env))]

        [(1st? e)  ;; (eval-exp (1st (apair (plus (num 4) (num 2)) (andalso (bool #t) (bool #f)))))
         (let ([v (eval-under-env-c (1st-e1 e) env)])
           (cond ((apair? v)(apair-e1 v))
                 (else (error "input doesn't evaluate to a pair"))))]
        
        [(2nd? e)  ;; (eval-exp (2nd (apair (plus (num 4) (num 2)) (andalso (bool #t) (bool #f)))))
         (let ([v (eval-under-env-c (2nd-e1 e) env)])
           (cond ((apair? v)(apair-e2 v))
                 (else (error "input doesn't evaluate to a pair"))))]

        [(ismunit? e)  ;; (eval-exp (ismunit (munit)))
         (cond ((munit? (eval-under-env-c (ismunit-e1 e) env))(bool #t))
               (else (bool #f)))]

        ;; NOTICE: In this NUMEX expression, the lam itself is put into the environment, not the closure. i.e. the function is not evaluated.
        ;; Therefore, (eval-exp (var "f")) would give us a lam, which must be evaluated one more time to give us a closure. That's the reason
        ;; we have two nested eval-exps in the semanticts of apply expression.
        [(letrec? e)
         (eval-under-env-c (letrec-e5 e)
                         (cons (cons (letrec-s1 e) (letrec-e1 e))
                         (cons (cons (letrec-s2 e) (letrec-e2 e))
                         (cons (cons (letrec-s3 e) (letrec-e3 e))
                         (cons (cons (letrec-s4 e) (letrec-e4 e)) env)))))]

        [(key? e) ;; (eval-exp (key "a" (plus (num 1) (num 2))))
         (key (key-s e) (eval-under-env-c (key-e e) env))]

        [(record? e)  ;; (eval-exp (record (key "b" (num 2)) (record (key "a" (num 1)) (munit))))
         (let ([v1 (eval-under-env-c (record-k e) env)]
               [v2 (eval-under-env-c (record-r e) env)])
           (cond ((key? v1) (cond ((or (munit? v2) (record? v2)) (record v1 v2))
                                  (else (error "the second argument is neither munit nor record"))))
                 (else (error "the frist argument is not a key"))))]


        [(value? e)
         (let ([r (eval-under-env-c (value-r e) env)])
           (cond ((record? r) (cond ((eq? (key-s (record-k r)) (value-s e)) (key-e (record-k r)))
                                    (else (cond ((record? (record-r r)) (eval-under-env-c (value (value-s e) (record-r r)) env))
                                                (else (munit))))))
                 (else (error "the second argument isn't a record."))))]

        
        [else (error (format "bad NUMEX expression: ~v" e))]))


;; Do NOT change this
(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))


;; SORT:
;; e.g. (eval-exp (apply sort (apair (num 1) (apair (num -4) (apair (num 5) (apair (num -1) (apair (num 3) (apair (num 2) (munit)))))))))

(define put-in-between
  (lam null "n" (lam "put" "lst"
                     (cnd (ismunit (var "lst")) (apair (var "n") (munit))
                          (ifleq (var "n") (1st (var "lst"))
                                 (apair (var "n") (var "lst"))
                                 (apair (1st (var "lst")) (apply (var "put") (2nd (var "lst")))))))))

(define sort
  (lam "sort" "list" (cnd (ismunit (var "list")) (munit)
                          (apply (apply put-in-between (1st (var "list"))) (apply (var "sort") (2nd (var "list")))))))


(define fun
  (lam null "formul"
       (cnd (iseq (with "x1" (bool #t) (with "x2" (bool #t) (var "formul") )) (bool #t))
            (bool #t)
            (cnd (iseq (with "x1" (bool #t) (with "x2" (bool #f) (var "formul") )) (bool #f))
                 (bool #t)
                 (cnd (iseq (with "x1" (bool #f) (with "x2" (bool #f) (var "formul") )) (bool #t))
                      (bool #t)
                      (cnd (iseq (with "x1" (bool #f) (with "x2" (bool #f) (var "formul") )) (bool #f))
                           (bool #t)
                           (bool #f)
                       )))))
)


(define test
  (andalso (var "x2") (neg (var "x1")))
)

