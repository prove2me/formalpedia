-- Prove2me | solution 1 for PI.PrimeLogOverPWork.le_log_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:59.894796+00:00
-- url     : https://prove2.me/submissions/87630347-4eaf-46dd-acff-cb60c054d2fc

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
theorem _root_.solution (p a b : ℕ) (hb : 0 < b) (h : 2 ^ a ≤ p ^ b) :
    (a : ℝ) / b * Real.log 2 ≤ Real.log (p : ℝ) := by
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · rw [zero_pow hb.ne'] at h
      have := Nat.one_le_two_pow (n := a)
      omega
    · exact hp
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h' : (2 : ℝ) ^ a ≤ (p : ℝ) ^ b := by exact_mod_cast h
  have h2 := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at h2
  rw [div_mul_eq_mul_div, div_le_iff₀ hb']
  linarith
end PI.PrimeLogOverPWork
