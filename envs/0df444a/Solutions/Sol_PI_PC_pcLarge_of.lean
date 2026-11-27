-- Prove2me | solution 1 for PI.PC.pcLarge_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:16:36.871805+00:00
-- url     : https://prove2.me/submissions/e0a89769-78c1-4081-b782-1f32c72abbeb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact
import Theorems.Thm_PI_PC_phi_intervalIntegrable
import Theorems.Thm_PI_PC_int_small
import Theorems.Thm_PI_PC_int_tail
import Theorems.Thm_PI_PC_gg_1024_nonneg
import Theorems.Thm_PI_PC_card_pr
import Theorems.Thm_PI_PC_log_131072_eq_seventeen_mul_log_two
import Theorems.Thm_PI_PC_log_sq_le

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
theorem _root_.solution (hU : CHUpper) : PCLarge 131072 := by
  intro y hy
  have hy0 : 0 < y := by linarith
  have hl2 : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hL : 17 * log 2 ≤ log y := by
    rw [← log_131072_eq_seventeen_mul_log_two]; exact Real.log_le_log (by norm_num) hy
  have hL' : 11.78 ≤ log y := by linarith
  have hLpos : 0 < log y := by linarith
  have hLne : log y ≠ 0 := hLpos.ne'
  have hL2 := log_sq_le hy
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (phi_intervalIntegrable (le_refl 2) (by norm_num : (2 : ℝ) ≤ 1024))
    (phi_intervalIntegrable (by norm_num) (by linarith : (1024 : ℝ) ≤ y))
  have hI : ∫ t in (2 : ℝ)..y, phi t ≤ 61 + gg y := by
    have h1 := int_small
    have h2 := int_tail hU (by linarith : (1024 : ℝ) ≤ y)
    have h3 := gg_1024_nonneg
    rw [← hsplit]
    linarith
  unfold gg at hI
  have hθ : Chebyshev.theta y ≤ 1.1056 * y + 0.7 * log y ^ 2 :=
    (Chebyshev.theta_le_psi y).trans (hU y (by linarith))
  have hdl : y / log y ^ 2 * log y = y / log y := by
    first | rw [pow_two, div_mul_eq_mul_div, mul_div_mul_right _ _ hLne] | (field_simp; ring) | field_simp
  have e : (61 + (1.56 * (y / log y ^ 2) + 0.7 * log y)) * log y =
      61 * log y + 1.56 * (y / log y) + 0.7 * log y ^ 2 := by
    rw [← hdl]; ring
  have hv : y / log y ≤ 0.085 * y := by
    rw [div_le_iff₀ hLpos]
    nlinarith [mul_le_mul_of_nonneg_left hL' hy0.le]
  have hLle : log y ≤ 0.00009 * y := by
    nlinarith [mul_le_mul_of_nonneg_left hL' hLpos.le]
  have key : Chebyshev.theta y + (61 + (1.56 * (y / log y ^ 2) + 0.7 * log y)) * log y < 1.26 * y := by
    nlinarith [e, hθ, hv, hLle, hL2, hy0]
  have hfin : Chebyshev.theta y / log y + (61 + (1.56 * (y / log y ^ 2) + 0.7 * log y)) < 1.26 * y / log y := by
    rw [div_add' _ _ _ hLne]
    first | exact div_lt_div_of_pos_right key hLpos | exact (div_lt_div_iff_of_pos_right hLpos).mpr key | gcongr
  rw [card_pr, Chebyshev.primeCounting_eq_theta_div_log_add_integral (by linarith)]
  show Chebyshev.theta y / log y + ∫ t in (2 : ℝ)..y, phi t < 1.26 * y / log y
  linarith
end PI.PC
