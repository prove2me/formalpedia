-- Prove2me | solution 1 for PI.PrimeLogOverPWork.log_le_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:46.887173+00:00
-- url     : https://prove2.me/submissions/e590aa95-e2cd-449d-a983-7764c5674d65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimeLogOverPWork
open Finset ArithmeticFunction Nat
namespace PI.PrimeLogOverPWork
theorem _root_.solution (p a b : ℕ) (hp : 0 < p) (hb : 0 < b) (h : p ^ b ≤ 2 ^ a) :
    Real.log (p : ℝ) ≤ (a : ℝ) / b * Real.log 2 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h' : (p : ℝ) ^ b ≤ (2 : ℝ) ^ a := by exact_mod_cast h
  have h2 := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ hb']
  linarith
end PI.PrimeLogOverPWork
