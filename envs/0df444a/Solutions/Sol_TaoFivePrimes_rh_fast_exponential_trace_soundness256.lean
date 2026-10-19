-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_exponential_trace_soundness256
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:42:35.976983+00:00
-- url     : https://prove2.me/submissions/257cb735-9a6f-46d6-b55f-ce7c1fb3203e

import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHFastExponentialTrace256Proof
open RHFastBallArithmetic RHFastBallSemantics RHFastBallFrequencyChecker256
noncomputable def P (m n:Nat) (z:ℂ):ℂ:=∑k∈Finset.range (n+1),z^k/(m.ascFactorial k:ℂ)
lemma first (m:Nat) (z:ℂ) : P m 0 z=1 := by simp [P]
lemma step (m n:Nat) (z:ℂ) : P m (n+1) z=1+z*P (m+1) n z/(m:ℂ) := by
 unfold P
 rw [Finset.sum_range_succ']
 simp only [pow_zero,Nat.ascFactorial_zero,Nat.cast_one,div_one]
 rw [Finset.mul_sum,Finset.sum_div,add_comm]
 congr 1
 apply Finset.sum_congr rfl
 intro k hk
 have hf:m.ascFactorial (k+1)=m*(m+1).ascFactorial k := by
  rw [Nat.ascFactorial_succ,←Nat.succ_ascFactorial]
 simp only [hf,Nat.cast_mul,pow_succ,div_eq_mul_inv,mul_inv_rev]
 ring
lemma checked (zball:Ball) (z:ℂ) (hz:encloses D zball z) (es:List Ball)
 (h0:entry es 0=integer D 1)
 (hs:∀n:Nat,n<40→entry es (n+1)=expStep zball n (entry es n)) :
 encloses D (entry es 40) (∑k∈Finset.range 41,z^k/(k.factorial:ℂ)) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D (by norm_num [D])
 have h (n:Nat) (hn:n≤40) : encloses D (entry es n) (P (41-n) n z) := by
  induction n with
  | zero=>rw [h0,first];simpa only [Int.cast_one] using S.integer_mem 1
  | succ n ih=>
   have hn':n<40:=by omega
   have hi:=ih (by omega)
   rw [hs n hn',expStep]
   have hf:=S.add_mem _ _ _ _ (S.integer_mem 1)
    (S.divide_mem _ _ (40-n) (by omega) (S.mul_mem _ _ _ _ hz hi))
   convert! hf using 1
   have he1:41-(n+1)=40-n:=by omega
   have he2:40-n+1=41-n:=by omega
   rw [he1,step,he2]
   norm_num only [Int.cast_one]
 have hf:=h 40 (by omega)
 simpa only [P,Nat.reduceSub,Nat.reduceAdd,Nat.one_ascFactorial] using hf
end RHFastExponentialTrace256Proof

theorem solution (zball:RHFastBallArithmetic.Ball) (z:ℂ)
 (hz:RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D zball z)
 (es:List RHFastBallArithmetic.Ball)
 (h0:RHFastBallFrequencyChecker256.entry es 0=RHFastBallArithmetic.integer RHFastBallFrequencyChecker256.D 1)
 (hs:∀n:Nat,n<40→RHFastBallFrequencyChecker256.entry es (n+1)=
  RHFastBallFrequencyChecker256.expStep zball n (RHFastBallFrequencyChecker256.entry es n)) :
 RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D (RHFastBallFrequencyChecker256.entry es 40)
  (∑k∈Finset.range 41,z^k/(k.factorial:ℂ)) := RHFastExponentialTrace256Proof.checked zball z hz es h0 hs
#print axioms solution
