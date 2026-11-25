-- Prove2me | solution 1 for PI.PC.psiUpperBound_of_lt_thirty_mul_six_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:14:56.151647+00:00
-- url     : https://prove2.me/submissions/f1a89b14-babe-4bf4-8187-6fc64be8b55c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiUpperBoundOfLtThirtyMulSixPow
import Theorems.Thm_PI_PC_log_six
import Theorems.Thm_PI_PC_psi_le_of_lt_thirty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PC
open Real
namespace PI.PC
theorem _root_.solution (hA : ANum) (hD : DUpper) (hS : Sandwich) (k : ℕ) :
    ∀ x : ℝ, 1 ≤ x → x < 30 * 6 ^ k → Chebyshev.psi x ≤ 1.1056 * x + 0.7 * (log x) ^ 2 := by
  induction k with
  | zero =>
    intro x h1 hx
    have := psi_le_of_lt_thirty (by linarith) (by simpa using hx)
    have := sq_nonneg (log x)
    linarith
  | succ k ih =>
    intro x h1 hx
    rcases lt_or_ge x 30 with h30 | h30
    · have := psi_le_of_lt_thirty (by linarith) h30
      have := sq_nonneg (log x)
      linarith
    · have hx6 : x / 6 < 30 * 6 ^ k := by
        rw [div_lt_iff₀ (by norm_num)]
        calc x < 30 * 6 ^ (k + 1) := hx
          _ = 30 * 6 ^ k * 6 := by ring
      have e1 := ih (x / 6) (by linarith) hx6
      have e2 := (hS x (by linarith)).1
      have e3 := hD x h30
      have e4 : chA * x ≤ 0.9213 * x := mul_le_mul_of_nonneg_right hA.2 (by linarith)
      have hl : log (x / 6) = log x - log 6 := log_div (by linarith) (by norm_num)
      rw [hl] at e1
      have hL : 0 ≤ log x := log_nonneg h1
      have l6a : 1.7917 ≤ log 6 := by
        rw [log_six]; have := log_two_gt_d9; have := log_three_gt_d9; norm_num at *; linarith
      have l6b : log 6 ≤ 1.7918 := by
        rw [log_six]; have := log_two_lt_d9; have := log_three_lt_d9; norm_num at *; linarith
      have p1 : 0 ≤ (1.4 * log 6 - 2.5) * log x := mul_nonneg (by linarith) hL
      have p2 : (log 6) ^ 2 ≤ 1.7918 ^ 2 := pow_le_pow_left₀ (by linarith) l6b 2
      nlinarith
end PI.PC
