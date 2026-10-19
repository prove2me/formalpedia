-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_ball_dot_product_soundness256
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:53:00.210665+00:00
-- url     : https://prove2.me/submissions/fbe9b68f-e37d-4503-9707-d414d0e3f49a

import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Mathlib.Data.List.Zip
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHFastDotProduct256Proof
open RHFastBallArithmetic RHFastBallSemantics RHFastBallFrequencyChecker256
lemma zip_range (as bs:List Ball) (hlen:as.length≤bs.length) :
 as.zip bs=(List.range as.length).map (fun i=>(entry as i,entry bs i)) := by
 apply List.ext_getElem
 · simp only [List.length_zip,List.length_map,List.length_range]
   omega
 · intro i hi1 hi2
   have hi:i<as.length:=by simpa only [List.length_map,List.length_range] using hi2
   have hj:i<bs.length:=by omega
   simp only [List.getElem_zip,List.getElem_map,List.getElem_range,entry,
    List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some]
lemma fold_sum (n:Nat) (f:Nat→ℂ) (z:ℂ) :
 (List.range n).foldl (fun a i=>a+f i) z=z+∑i∈Finset.range n,f i := by
 induction n with
 | zero=>simp
 | succ n ih=>
  simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih,Finset.sum_range_succ]
  ring
lemma fold_mem {I:Type*} (is:List I) (f:I→Ball) (g:I→ℂ)
 (a:Ball) (z:ℂ) (ha:encloses D a z) :
 (∀i∈is,encloses D (f i) (g i))→
 encloses D (is.foldl (fun a i=>add a (f i)) a)
  (is.foldl (fun z i=>z+g i) z) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D (by norm_num [D])
 induction is generalizing a z with
 | nil=>intro h;exact ha
 | cons i is ih=>
  intro h
  apply ih _ _ (S.add_mem _ _ _ _ ha (h i (by simp)))
  intro j hj
  exact h j (by simp [hj])
lemma contained (as bs:List Ball) (f g:Nat→ℂ) (hlen:as.length≤bs.length)
 (ha:∀i:Nat,i<as.length→encloses D (entry as i) (f i))
 (hb:∀i:Nat,i<as.length→encloses D (entry bs i) (g i)) :
 encloses D (dot as bs) (∑i∈Finset.range as.length,f i*g i) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D (by norm_num [D])
 unfold dot
 rw [zip_range as bs hlen,List.foldl_map]
 have h:=fold_mem (List.range as.length) (fun i=>mul D (entry as i) (entry bs i)) (fun i=>f i*g i) zero 0
  (by simp [encloses,value,zero]) (fun i hi=>S.mul_mem _ _ _ _ (ha i (List.mem_range.mp hi)) (hb i (List.mem_range.mp hi)))
 simpa only [fold_sum,zero_add] using h
end RHFastDotProduct256Proof

theorem solution (as bs:List RHFastBallArithmetic.Ball) (f g:Nat→ℂ) (hlen:as.length≤bs.length)
 (ha:∀i:Nat,i<as.length→RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D (RHFastBallFrequencyChecker256.entry as i) (f i))
 (hb:∀i:Nat,i<as.length→RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D (RHFastBallFrequencyChecker256.entry bs i) (g i)) :
 RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D (RHFastBallFrequencyChecker256.dot as bs)
  (∑i∈Finset.range as.length,f i*g i) := RHFastDotProduct256Proof.contained as bs f g hlen ha hb
#print axioms solution
