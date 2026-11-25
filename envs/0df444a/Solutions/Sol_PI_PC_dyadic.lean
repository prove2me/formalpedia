-- Prove2me | solution 1 for PI.PC.dyadic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:18.78957+00:00
-- url     : https://prove2.me/submissions/9663ec0e-4d96-41df-93ad-817966c16ac2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact
import Theorems.Thm_PI_PC_phi_intervalIntegrable
import Theorems.Thm_PI_PC_piece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Real MeasureTheory Set
namespace PI.PC
theorem _root_.solution (k : ℕ) : ∫ t in (2 : ℝ)..2 ^ (k + 1), phi t ≤
    2 / log 2 * ∑ i ∈ Finset.range k, (2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hl2' : log 2 ≠ 0 := hl2.ne'
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have ha : (2 : ℝ) ≤ 2 ^ (k + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hb : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (k + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (phi_intervalIntegrable (le_refl 2) ha) (phi_intervalIntegrable ha hb)
    have hpiece : ∫ t in (2 : ℝ) ^ (k + 1)..2 ^ (k + 1 + 1), phi t ≤
        log 4 / (((k : ℝ) + 1) * log 2) ^ 2 * (2 ^ (k + 1 + 1) - 2 ^ (k + 1)) :=
      piece ha hb (mul_pos (by positivity) hl2)
        (by rw [Real.log_pow]; norm_num)
    have h4 : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have heq : log 4 / (((k : ℝ) + 1) * log 2) ^ 2 * (2 ^ (k + 1 + 1) - 2 ^ (k + 1)) =
        2 / log 2 * ((2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) ^ 2) := by
      rw [h4]; first | (field_simp; ring) | field_simp
    rw [← hsplit, Finset.sum_range_succ, mul_add]
    linarith
end PI.PC
