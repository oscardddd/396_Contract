#lang racket
(require redex)


(define-language CON
  (p ::= (d ... e))
  (d ::= (declare x e e))
  (dv ::= (declare x V V))
  (e ::=  x (λ (x) e) (e e) x (fix x e) n (aop e e) (rop e e) (cop e) (cons e e) mt (head e) (tail e) (mt? e)
     (ifthenelse e e e) true false str (func e e) (contract e) (flatp e) (pred e) (dom e) (rng e) (blame e) (error str)
     (obligation e e str str))
  
  (n ::= integer)
  (str ::= string)
  (x y z ::= variable-not-otherwise-mentioned)
  (op ::= rop aop cop)
  (rop ::= add mult subtract divide)
  (aop ::= gequal equal)
  (cop ::= num? str?)
  (t ::= (func t t) int st bool (lst t) (contract t))

  (E ::= hole (E e) (V E) (aop E e) (aop V E) (rop E e) (rop V E) (cop E) (cons E e) (cons V E) (head E) (tail E)
     (ifthenelse E e e) (func E e) (func V E) (contract E) (flatp E) (pred E) (dom E) (rng E) (blame E)
     (obligation e E str str) (obligation E V str str))
  
  (r ::= (add V V) ((λ(x) e) V))

  (P ::= (dv ... (declare x E e) d ... e) (dv ... (deeclare x V E) d ... e) (dv ... E))

  (V ::= (cons V V) (λ (x) e) str n true false (func V V) (contract V) (obligation V (func V V) str str))
  (Vp ::= (dv ... V))
  
  #:binding-forms
  (λ (x) e #:refers-to x)
  )

;(redex-match CON (in-hole P (V_1 V_2)) (term ((declare f (func (contract (λ (x) ,(number? (term x)))) (contract (λ (x) true))) (λ (x) x)) ((λ (x) 1) (obligation 1 (contract (number? 1)) "main" "one")))))

;(redex-match CON (in-hole P (V_1 V_2)) (term ((declare f (func (contract (λ (x) true)) (contract (λ (x) true))) (λ (x) x)) (f 1))))
; (redex-match CON V (term (obligation (λ (x) 1) (func (contrast (λ (x) true)) (contrast (λ (x) true))))))


;(redex-match CON (in-hole P e) (term ((declare f (func (contract (λ (x) true)) (contract (λ (x) true))) (λ (x) x)) ((λ (x) 1) 1))))
;(redex-match CON (a )

;(redex-match CON (in-hole P r) (term ((declare f (contract (add 1 1)) 1) 1)))





(define-metafunction CON
  getdec : p -> (d ...)
  [(getdec (d ... e)) (d ...)])

(define-metafunction CON
  findvalue : p x -> e 
  ;[(findvalue ((declare x V_1 V_2) d ... e) x)
  ;V_2]
  [(findvalue ((declare x V_1 V_2) d ... e) x)
   (obligation V_2 V_1 "function" "main")]
   
  [(findvalue (d_1 d ... e) x) (findvalue (d ... e) x)])


(default-language CON)


;(define-metafunction CON
; check : dv ... E -> V)


(define-metafunction CON
  delta : op V ... -> V
  [(delta divide V_1 0) (error "divide by zero")]
  [(delta add V_1 V_2) ,(+ (term V_1) (term V_2))]
  [(delta subtract V_1 V_2) ,(- (term V_1) (term V_2))]
  [(delta mult V_1 V_2) ,(* (term V_1) (term V_2))]
  [(delta equal V_1 V_2) ,(if (equal? (term V_1) (term V_2)) 'true 'false) ]
  [(delta gequal V_1 V_2) ,(if (>= (term V_1) (term V_2)) 'true 'false)]
  [(delta num? V_1) ,(if (number? (term V_1)) 'true 'false)]
  [(delta str? V_1) ,(string? (term V_1))]
  )
 

(define ->CV
  (reduction-relation
   CON
   [-->  (in-hole P ((λ (x) e) V))
         (in-hole P (substitute e x V)) β]
   
   [-->  (in-hole P (op V ...))
         (in-hole P (delta op V ...))
         δ]

   ; [--> (in-hole P (declare x e_1 e_2))
   ;(in-hole P (e_2))]

   
   ; this one is the one that we add obligation into the story
   [--> (in-hole P x)
        (in-hole P (findvalue (in-hole P x) x))]
   
   
   [--> (in-hole P (ifthenelse true e_1 e_2))
        (in-hole P e_1)]
   
   [--> (in-hole P (ifthenelse false e_1 e_2))
        (in-hole P e_2)]

   [--> (in-hole P (head (cons e_1 e_2)))
        (in-hole P e_1)]
   
   [--> (in-hole P (head mt) )
        (error "get head of an empty")]
   
   [--> (in-hole P (tail (cons e_1 e_2)))
        (in-hole P e_2)]

   [--> (in-hole P (tail mt) )
        (error "get tail of an empty")]

   [--> (in-hole P (mt? mt))
        (in-hole P true)]
   
   [--> (in-hole P (mt? (cons e_1 e_2)))
        (in-hole P false)] 
   
   [--> (in-hole P (flatp (contract e)))
        (in-hole P true)]

   [--> (in-hole P (flatp (func e_1 e_2)))
        (in-hole P false)]
   
   [--> (in-hole P (pred (contract e)))
        (in-hole P e)]
   
   [--> (in-hole P (pred (func e_1 e_2)))
        (error "not a predicate contract")]

   [--> (in-hole P (dom (func e_1 e_2)))
        (in-hole P e_1)]

   [--> (in-hole P (dom (contract e)))
        (error "get domain of predicate contract")]

   [--> (in-hole P (rng (func e_1 e_2)))
        (in-hole P e_2)]

   [--> (in-hole P (rng (contract e)))
        (error "get range of a predicate contract")]

   [--> (in-hole P (blame str))
        (error str)]

   ;obligation reduction 1
   [--> (in-hole P (obligation V_1 (contract V_2) str_1 str_2))
        (in-hole P (ifthenelse (V_2 V_1) V_1 (blame str_1)))]
   
   ;obligation reduction 2
   [--> (in-hole P ((obligation V_1 (func V_3 V_4) str_1 str_2) V_2))
        (in-hole P (obligation (V_1 (obligation V_2 V_3 str_2 str_1)) V_4 str_1 str_2))]


   ))

(test-match CON V (term (λ (x) x)))


(test-match CON V (term 1))


; (apply-reduction-relation* (term (declare x (contract x) "wrong" "main")) ->CV)

(redex-match CON p (term((declare x (contract (λ (x) (num? x)))10) x)))

;(traces ->CV (term (add 1 1 )))

(redex-match CON (in-hole P (V_1 V_2)) (term((declare
                                              x
                                              (contract (λ (x) true))
                                              10)
                                             (ifthenelse
                                              ((λ (x) true) 10)
                                              10
                                              (blame "function")))))


(redex-match CON  (in-hole E (V_1 V_2)) (term
                                         (ifthenelse
                                          ((λ (x) true) 10)
                                          10
                                          (blame "function"))))



(redex-match CON e (term (num? 10)))


; Here comes all the examples:

;(traces ->CV (term ((declare f (func (contract (λ (x) (num? x))) (contract (λ (y) true))) (λ (x) 10)) (f 1))))
;
;;flat contract
;(traces ->CV (term ((declare x (contract (λ (x) (num? x)))10)x)))
;
;;square
;(traces ->CV (term ((declare sq (func (contract (λ (x) (num? x))) (contract (λ (y) (num? y)))) (λ (x) (mult x x))) (sq 2))))
;(traces ->CV (term ((declare sq (func (contract (λ (x) (num? x))) (contract (λ (y) (num? y)))) (λ (x) (mult x x))) (sq "1"))))
;(traces ->CV (term ((declare sq (func (contract (λ (x) (num? x))) (contract (λ (y) (num? y)))) (λ (x) "1")) (sq 2))))
;(traces ->CV (term ((declare sq (func (contract (λ (x) (num? x))) (contract (λ (y) (gequal y 0)))) (λ (x) (mult x x))) (sq 2))))

;derive
;(traces ->CV (term ((declare derive (func
;                                    (func (contract (λ (x) (num? x))) (contract (λ (y) (num? y))))
;                                    (contract (λ (z) (num? z)))
;                                    )
;                             (λ (f) (f 5)))
;                    (derive (λ (x) (mult x x))))))
;
;(traces ->CV (term ((declare derive (func
;                                    (func (contract (λ (x) (num? x))) (contract (λ (y) (num? y))))
;                                    (contract (λ (z) (num? z)))
;                                    )
;                             (λ (f) (f "1")))
;                    (derive (λ (x) (mult x x))))))
;
;
;(traces ->CV (term ((declare derive (func
;                                    (func (contract (λ (x) (num? x))) (contract (λ (y) (num? y))))
;                                    (contract (λ (z) (num? z)))
;                                    )
;                             (λ (f) (f 1)))
;                    (derive (λ (x) "1")))))


;derive2
;(traces ->CV (term ((declare derive (func
;                                    (contract (λ (z) (equal z 1)))
;                                    (func (contract (λ (x) (num? x))) (contract (λ (y) (num? y))))
;                                    )
;                             (λ (x) (λ (y) (mult x y))))
;                    ((derive 1) 2))))
;
;(traces ->CV (term ((declare derive (func
;                                    (contract (λ (z) (equal z 1)))
;                                    (func (contract (λ (x) (num? x))) (contract (λ (y) (num? y))))
;                                    )
;                             (λ (x) (λ (y) y)))
;                    ((derive 1) "1"))))
;
;(traces ->CV (term ((declare derive (func
;                                    (contract (λ (z) (equal z 1)))
;                                    (func (contract (λ (x) (num? x))) (contract (λ (y) (num? y))))
;                                    )
;                             (λ (x) (λ (y) "1")))
;                    ((derive 1) 2))))
;
;(traces ->CV (term ((declare derive (func
;                                    (contract (λ (z) (equal z 1)))
;                                    (func (contract (λ (x) (num? x))) (contract (λ (y) (num? y))))
;                                    )
;                             (λ (x) (λ (y) "1")))
;                    (derive 1))))


(test-results)



