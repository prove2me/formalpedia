-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_ball_polynomial_list_containment
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:31:01.073972+00:00
-- url     : https://prove2.me/submissions/41bfe058-fc3f-4302-9a62-86cb5f7cc7ec

import Definitions.Def_TaoFivePrimes_RHFastBallPolynomialArithmetic
import Definitions.Def_TaoFivePrimes_RHFastComplexPolynomialLists
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHFastBallPolynomialListProof
open RHFastBallArithmetic RHFastBallSemantics
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
lemma add_mem (D:Nat) (hD:0<D) (xs:List Ball) (us:List ℂ) (ys:List Ball) (vs:List ℂ)
 (hx:List.Forall₂ (encloses D) xs us) (hy:List.Forall₂ (encloses D) ys vs) :
 List.Forall₂ (encloses D) (RHFastBallPoly.addList xs ys) (RHFastComplexPoly.addList us vs) := by
 unfold RHFastBallPoly.addList RHFastComplexPoly.addList
 rw [hx.length_eq,hy.length_eq]
 apply map_mem
 intro i
 exact (TaoFivePrimes.rh_fast_complex_ball_soundness D hD).add_mem _ _ _ _
  (entry_mem D hx i) (entry_mem D hy i)
lemma mulCoeff_mem (D:Nat) (hD:0<D) (xs:List Ball) (us:List ℂ) (ys:List Ball) (vs:List ℂ)
 (hx:List.Forall₂ (encloses D) xs us) (hy:List.Forall₂ (encloses D) ys vs) (k:Nat) :
 encloses D (RHFastBallPoly.mulCoeff D xs ys k) (RHFastComplexPoly.mulCoeff us vs k) := by
 let f:Nat→Ball:=fun i=>if i<xs.length ∧ i≤k ∧ k-i<ys.length then
  mul D (RHFastBallPoly.entry xs i) (RHFastBallPoly.entry ys (k-i)) else zero
 let g:Nat→ℂ:=fun i=>if i<us.length ∧ i≤k ∧ k-i<vs.length then
  RHFastComplexPoly.entry us i*RHFastComplexPoly.entry vs (k-i) else 0
 have h:∀i,encloses D (f i) (g i) := by
  intro i
  dsimp only [f,g]
  rw [hx.length_eq,hy.length_eq]
  split_ifs
  · exact (TaoFivePrimes.rh_fast_complex_ball_soundness D hD).mul_mem _ _ _ _
     (entry_mem D hx i) (entry_mem D hy (k-i))
  · exact zero_mem D
 simpa only [RHFastBallPoly.mulCoeff,RHFastComplexPoly.mulCoeff,f,g] using
  fold_range_mem D hD (k+1) f g h
lemma mul_mem (D:Nat) (hD:0<D) (xs:List Ball) (us:List ℂ) (ys:List Ball) (vs:List ℂ)
 (hx:List.Forall₂ (encloses D) xs us) (hy:List.Forall₂ (encloses D) ys vs) :
 List.Forall₂ (encloses D) (RHFastBallPoly.mulList D xs ys) (RHFastComplexPoly.mulList us vs) := by
 unfold RHFastBallPoly.mulList RHFastComplexPoly.mulList
 rw [hx.length_eq,hy.length_eq]
 apply map_mem
 intro k
 exact mulCoeff_mem D hD xs us ys vs hx hy k
lemma divide_mem (D:Nat) (hD:0<D) (xs:List Ball) (us:List ℂ) (n:Nat) (hn:0<n)
 (hx:List.Forall₂ (encloses D) xs us) :
 List.Forall₂ (encloses D) (RHFastBallPoly.divideList xs n) (RHFastComplexPoly.divideList us n) := by
 induction hx with
 | nil=>exact List.Forall₂.nil
 | cons ha ht ih=>
  exact List.Forall₂.cons
   ((TaoFivePrimes.rh_fast_complex_ball_soundness D hD).divide_mem _ _ n hn ha) ih
end RHFastBallPolynomialListProof

theorem solution (D:Nat) (hD:0<D) :
 (∀(xs:List RHFastBallArithmetic.Ball)(us:List ℂ)(ys:List RHFastBallArithmetic.Ball)(vs:List ℂ),
  List.Forall₂ (RHFastBallSemantics.encloses D) xs us → List.Forall₂ (RHFastBallSemantics.encloses D) ys vs →
  List.Forall₂ (RHFastBallSemantics.encloses D) (RHFastBallPoly.addList xs ys) (RHFastComplexPoly.addList us vs)) ∧
 (∀(xs:List RHFastBallArithmetic.Ball)(us:List ℂ)(ys:List RHFastBallArithmetic.Ball)(vs:List ℂ),
  List.Forall₂ (RHFastBallSemantics.encloses D) xs us → List.Forall₂ (RHFastBallSemantics.encloses D) ys vs →
  List.Forall₂ (RHFastBallSemantics.encloses D) (RHFastBallPoly.mulList D xs ys) (RHFastComplexPoly.mulList us vs)) ∧
 (∀(xs:List RHFastBallArithmetic.Ball)(us:List ℂ)(n:Nat),0<n →
  List.Forall₂ (RHFastBallSemantics.encloses D) xs us →
  List.Forall₂ (RHFastBallSemantics.encloses D) (RHFastBallPoly.divideList xs n) (RHFastComplexPoly.divideList us n)) :=
 ⟨RHFastBallPolynomialListProof.add_mem D hD,RHFastBallPolynomialListProof.mul_mem D hD,
  RHFastBallPolynomialListProof.divide_mem D hD⟩
#print axioms solution
