-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_polynomial_circuit_soundness
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:42:33.963548+00:00
-- url     : https://prove2.me/submissions/f173ea8f-ad1e-470b-8557-61233b7704f7

import Definitions.Def_TaoFivePrimes_RHFastPolynomialCircuitSemantics
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_ball_polynomial_list_containment
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_polynomial_list_algebra
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex Finset Polynomial
namespace RHFastCircuitSoundnessProof
open RHFastBallArithmetic RHFastBallSemantics RHFastComplexPoly
lemma entry_none (xs:List ℂ) (k:Nat) (hk:xs.length≤k) : entry xs k=0 := by
 simp only [entry,List.getElem?_eq_none hk,Option.getD_none]
lemma entry_tabulate (f:Nat→ℂ) (n k:Nat) (hk:k<n) :
 entry ((List.range n).map f) k=f k := by
 simp only [entry,List.getElem?_map,List.getElem?_range hk,Option.map_some,Option.getD_some]
lemma coeff_polynomial (xs:List ℂ) (k:Nat) : (polynomial xs).coeff k=entry xs k := by
 unfold polynomial
 rw [Polynomial.finsetSum_coeff]
 simp only [Polynomial.coeff_C_mul_X_pow]
 by_cases hk:k<xs.length
 · simpa only [Finset.sum_ite_eq,Finset.mem_range,if_pos hk]
 · rw [entry_none xs k (by omega)]
   simpa only [Finset.sum_ite_eq,Finset.mem_range,if_neg hk]
lemma polynomial_singleton (a:ℂ) : polynomial [a]=Polynomial.C a := by
 ext k
 rw [coeff_polynomial,Polynomial.coeff_C]
 cases k with
 | zero=>simp [entry]
 | succ k=>simp [entry]
lemma zero_mem (D:Nat) : encloses D zero (0:ℂ) := by simp [encloses,value,zero]
lemma entry_mem (D:Nat) {xs:List Ball} {us:List ℂ}
 (h:List.Forall₂ (encloses D) xs us) (i:Nat) :
 encloses D (RHFastBallPoly.entry xs i) (RHFastComplexPoly.entry us i) := by
 induction h generalizing i with
 | nil=>simpa [RHFastBallPoly.entry,RHFastComplexPoly.entry] using zero_mem D
 | cons ha ht ih=>
  cases i with
  | zero=>simpa [RHFastBallPoly.entry,RHFastComplexPoly.entry] using ha
  | succ i=>simpa [RHFastBallPoly.entry,RHFastComplexPoly.entry] using ih i
lemma map_mem (D:Nat) {I:Type*} (is:List I) (f:I→Ball) (g:I→ℂ)
 (h:∀i,encloses D (f i) (g i)) :
 List.Forall₂ (encloses D) (is.map f) (is.map g) := by
 induction is with
 | nil=>exact List.Forall₂.nil
 | cons i is ih=>exact List.Forall₂.cons (h i) ih
lemma fold_mem (D:Nat) (hD:0<D) {I:Type*} (is:List I) (f:I→Ball) (g:I→ℂ)
 (h:∀i,encloses D (f i) (g i)) (a:Ball) (z:ℂ) (ha:encloses D a z) :
 encloses D (is.foldl (fun a i=>add a (f i)) a)
  (is.foldl (fun z i=>z+g i) z) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D hD
 induction is generalizing a z with
 | nil=>exact ha
 | cons i is ih=>
  exact ih _ _ (S.add_mem _ _ _ _ ha (h i))
lemma fold_range_sum (n:Nat) (f:Nat→ℂ) (z:ℂ) :
 (List.range n).foldl (fun a i=>a+f i) z=z+∑i∈Finset.range n,f i := by
 induction n with
 | zero=>simp
 | succ n ih=>
  simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih,Finset.sum_range_succ]
  ring
lemma fold_range_mem (D:Nat) (hD:0<D) (n:Nat) (f:Nat→Ball) (g:Nat→ℂ)
 (h:∀i,encloses D (f i) (g i)) :
 encloses D ((List.range n).foldl (fun a i=>add a (f i)) zero)
  (∑i∈Finset.range n,g i) := by
 have hs:=fold_mem D hD (List.range n) f g h zero 0 (zero_mem D)
 simpa only [fold_range_sum,zero_add] using hs
lemma polynomial_X : RHFastComplexPoly.polynomial [0,1]=(Polynomial.X:Polynomial ℂ) := by
 apply Polynomial.ext
 intro k
 rw [coeff_polynomial,Polynomial.coeff_X]
 cases k with
 | zero=>simp [RHFastComplexPoly.entry]
 | succ k=>cases k with
   | zero=>simp [RHFastComplexPoly.entry]
   | succ k=>simp [RHFastComplexPoly.entry]
lemma power_mem (D:Nat) (hD:0<D) (as:List Ball) (zs:List ℂ)
 (h:List.Forall₂ (encloses D) as zs) (n:Nat) :
 List.Forall₂ (encloses D) (RHFastPolynomialCircuit.powerList D as n)
   (RHFastPolynomialCircuitSemantics.powerList zs n) := by
 induction n with
 | zero=>
  exact List.Forall₂.cons
   (by simpa only [Int.cast_one] using (TaoFivePrimes.rh_fast_complex_ball_soundness D hD).integer_mem 1) List.Forall₂.nil
 | succ n ih=>exact (TaoFivePrimes.rh_fast_ball_polynomial_list_containment D hD).2.1 _ _ _ _ ih h
lemma power_polynomial (zs:List ℂ) (n:Nat) :
 RHFastComplexPoly.polynomial (RHFastPolynomialCircuitSemantics.powerList zs n)=
   (RHFastComplexPoly.polynomial zs)^n := by
 induction n with
 | zero=>simpa only [RHFastPolynomialCircuitSemantics.powerList,polynomial_singleton,map_one,pow_zero]
 | succ n ih=>rw [RHFastPolynomialCircuitSemantics.powerList,
   (TaoFivePrimes.rh_fast_complex_polynomial_list_algebra _ _ 1).2.1,ih,pow_succ]
lemma contained (D:Nat) (hD:0<D) (as:List Ball) (zs:List ℂ)
 (h:List.Forall₂ (encloses D) as zs) (e:RHFastPolynomialCircuit.Expr) :
 List.Forall₂ (encloses D) (RHFastPolynomialCircuit.evaluate D as e)
   (RHFastPolynomialCircuitSemantics.evaluate zs e) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D hD
 let P:=TaoFivePrimes.rh_fast_ball_polynomial_list_containment D hD
 induction e with
 | zero=>exact List.Forall₂.cons (zero_mem D) List.Forall₂.nil
 | one=>exact List.Forall₂.cons (by simpa only [Int.cast_one] using S.integer_mem 1) List.Forall₂.nil
 | imag=>
  apply List.Forall₂.cons _ List.Forall₂.nil
  have hi:=S.rotate_mem _ _ 3 (S.integer_mem 1)
  simpa only [Nat.reduceMod,Int.cast_one,mul_one,show (-I)^3=I by norm_num [pow_succ,pow_two]] using hi
 | «variable»=>exact List.Forall₂.cons (zero_mem D) (List.Forall₂.cons (by simpa only [Int.cast_one] using S.integer_mem 1) List.Forall₂.nil)
 | input i=>exact List.Forall₂.cons (entry_mem D h i) List.Forall₂.nil
 | rational p q=>
  simpa only [RHFastPolynomialCircuit.evaluate,RHFastPolynomialCircuitSemantics.evaluate,Nat.cast_add,Nat.cast_one] using
   List.Forall₂.cons (S.rational_mem p (q+1) (by omega)) List.Forall₂.nil
 | add a b ha hb=>exact P.1 _ _ _ _ ha hb
 | mul a b ha hb=>exact P.2.1 _ _ _ _ ha hb
 | divide a n ha=>exact P.2.2 _ _ (n+1) (by omega) ha
 | power a n ha=>exact power_mem D hD _ _ ha n
lemma interpreted (zs:List ℂ) (e:RHFastPolynomialCircuit.Expr) :
 RHFastComplexPoly.polynomial (RHFastPolynomialCircuitSemantics.evaluate zs e)=
   RHFastPolynomialCircuitSemantics.polynomial zs e := by
 induction e with
 | zero=>simpa only [RHFastPolynomialCircuitSemantics.evaluate,RHFastPolynomialCircuitSemantics.polynomial,polynomial_singleton,map_zero]
 | one=>simpa only [RHFastPolynomialCircuitSemantics.evaluate,RHFastPolynomialCircuitSemantics.polynomial,polynomial_singleton,map_one]
 | imag=>exact polynomial_singleton _
 | «variable»=>exact polynomial_X
 | input i=>exact polynomial_singleton _
 | rational p q=>exact polynomial_singleton _
 | add a b ha hb=>rw [RHFastPolynomialCircuitSemantics.evaluate,
   (TaoFivePrimes.rh_fast_complex_polynomial_list_algebra _ _ 1).1,ha,hb];rfl
 | mul a b ha hb=>rw [RHFastPolynomialCircuitSemantics.evaluate,
   (TaoFivePrimes.rh_fast_complex_polynomial_list_algebra _ _ 1).2.1,ha,hb];rfl
 | divide a n ha=>
  rw [RHFastPolynomialCircuitSemantics.evaluate,
   (TaoFivePrimes.rh_fast_complex_polynomial_list_algebra _ [] (n+1)).2.2,ha]
  simp only [RHFastPolynomialCircuitSemantics.polynomial,Nat.cast_add,Nat.cast_one]
 | power a n ha=>rw [RHFastPolynomialCircuitSemantics.evaluate,power_polynomial,ha];rfl
end RHFastCircuitSoundnessProof

theorem solution (D:Nat) (hD:0<D) (as:List RHFastBallArithmetic.Ball) (zs:List ℂ)
 (h:List.Forall₂ (RHFastBallSemantics.encloses D) as zs) (e:RHFastPolynomialCircuit.Expr) :
 List.Forall₂ (RHFastBallSemantics.encloses D) (RHFastPolynomialCircuit.evaluate D as e)
   (RHFastPolynomialCircuitSemantics.evaluate zs e) ∧
 RHFastComplexPoly.polynomial (RHFastPolynomialCircuitSemantics.evaluate zs e)=
   RHFastPolynomialCircuitSemantics.polynomial zs e :=
 ⟨RHFastCircuitSoundnessProof.contained D hD as zs h e,RHFastCircuitSoundnessProof.interpreted zs e⟩
#print axioms solution
