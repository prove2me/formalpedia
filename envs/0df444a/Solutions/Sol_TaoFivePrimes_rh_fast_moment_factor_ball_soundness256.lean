-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_moment_factor_ball_soundness256
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:50:34.582364+00:00
-- url     : https://prove2.me/submissions/736c14b7-2758-4e74-b386-99f066d154e1

import Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex
namespace RHFastMomentFactor256Proof
open RHFastBallArithmetic RHFastBallSemantics RHFastWindow256Setup
lemma contained (pi:Ball) (hpi:encloses D pi (Real.pi:ℂ)) (k:Nat) :
 encloses D (factor pi k) (((-Real.pi:ℝ):ℂ)^k/(k.factorial:ℂ)) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D (by norm_num [D])
 induction k with
 | zero=>simpa only [factor,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,Int.cast_one] using S.integer_mem 1
 | succ k ih=>
  have h:=S.divide_mem _ _ (k+1) (by omega)
   (S.mul_mem _ _ _ _ ih (S.neg_mem _ _ hpi))
  convert! h using 1
  simp only [Nat.factorial_succ,Nat.cast_mul,pow_succ,Complex.ofReal_neg]
  simp only [div_eq_mul_inv,mul_inv_rev,Nat.cast_add,Nat.cast_one]
  ring
end RHFastMomentFactor256Proof

theorem solution (pi:RHFastBallArithmetic.Ball)
 (hpi:RHFastBallSemantics.encloses RHFastWindow256Setup.D pi (Real.pi:ℂ)) (k:Nat) :
 RHFastBallSemantics.encloses RHFastWindow256Setup.D (RHFastWindow256Setup.factor pi k)
  (((-Real.pi:ℝ):ℂ)^k/(k.factorial:ℂ)) := RHFastMomentFactor256Proof.contained pi hpi k
#print axioms solution
