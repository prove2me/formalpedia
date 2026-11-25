-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.ker_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:19:10.357422+00:00
-- url     : https://prove2.me/submissions/284a7116-8228-4edd-90c0-90c546107c62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PlanarKernelBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Real
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals
theorem _root_.solution (e γ : ℝ) (he : 0 < e) (heγ : e < γ) (hγ : γ < 2) (c : ℂ) (D ρ : ℝ) (hρ : 0 < ρ)
    (hρc : ‖c‖ ≤ 2 * ρ) (hDρ : D ^ 2 = 4 * ρ ^ 2 - ‖c‖ ^ 2) (x : ℂ) (hx0 : x ≠ 0) (hxc : x ≠ c) :
    ENNReal.ofReal ((‖x - c‖ ^ 2 + D ^ 2) ^ (-1 + e / 2)) * ENNReal.ofReal (‖x‖ ^ (-γ)) ≤
      ENNReal.ofReal ((ρ ^ 2) ^ (-1 + e / 2)) *
          (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-γ))) ‖x‖ +
        ENNReal.ofReal ((4 : ℝ) ^ (-(-1 + e / 2))) *
          (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-(2 + γ - e)))) ‖x‖ +
        ENNReal.ofReal (ρ ^ (-γ)) *
          (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖x - c‖ := by
  have hE : -1 + e / 2 ≤ 0 := by linarith
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hm : 0 < ‖x - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hxc)
  have t1 : ‖c‖ - ‖x‖ ≤ ‖x - c‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le c x
  have t2 : ‖x‖ - ‖c‖ ≤ ‖x - c‖ := norm_sub_norm_le x c
  have t3 : ‖x - c‖ ≤ ‖x‖ + ‖c‖ := norm_sub_le x c
  rcases le_or_gt ‖x‖ ρ with hA | hA
  · have hle : ρ ^ 2 ≤ ‖x - c‖ ^ 2 + D ^ 2 := by
      rcases le_or_gt ‖c‖ ρ with h | h
      · nlinarith [norm_nonneg c, sq_nonneg ‖x - c‖, mul_le_mul h h (norm_nonneg c) hρ.le]
      · have h' : ‖c‖ - ρ ≤ ‖x - c‖ := by linarith
        nlinarith [mul_le_mul h' h' (by linarith) (norm_nonneg _), mul_le_mul_of_nonneg_left hρc hρ.le]
    refine le_add_right (le_add_right ?_)
    rw [indicator_of_mem (show ‖x‖ ∈ Iic ρ from hA)]
    exact mul_le_mul'
      (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) hle hE)) le_rfl
  rcases le_or_gt (2 * ‖c‖) ‖x‖ with hB | hB
  · refine le_add_right (le_add_left ?_)
    rw [indicator_of_mem (show ‖x‖ ∈ Ioi ρ from hA)]
    have h' : ‖x‖ / 2 ≤ ‖x - c‖ := by linarith
    have hle : ‖x‖ ^ 2 / 4 ≤ ‖x - c‖ ^ 2 + D ^ 2 := by
      nlinarith [mul_le_mul h' h' (by positivity) (norm_nonneg _), sq_nonneg D]
    have hid : (‖x‖ ^ 2 / 4) ^ (-1 + e / 2) * ‖x‖ ^ (-γ) =
        (4 : ℝ) ^ (-(-1 + e / 2)) * ‖x‖ ^ (-(2 + γ - e)) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_two, ← Real.rpow_mul hn.le,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
      have h2 : ‖x‖ ^ (2 * (-1 + e / 2)) * ‖x‖ ^ (-γ) = ‖x‖ ^ (-(2 + γ - e)) := by
        rw [← Real.rpow_add hn]; congr 1; ring
      rw [← h2, div_eq_mul_inv]; ring
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← hid]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos (by positivity) hle hE) (by positivity))
  · refine le_add_left ?_
    have h6 : ‖x - c‖ ≤ 6 * ρ := by linarith
    rw [indicator_of_mem (show ‖x - c‖ ∈ Iic (6 * ρ) from h6)]
    have hid : (‖x - c‖ ^ 2) ^ (-1 + e / 2) = ‖x - c‖ ^ (-(2 - e)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hm.le]; congr 1; ring
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← hid,
      mul_comm (ρ ^ (-γ))]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul
      (Real.rpow_le_rpow_of_nonpos (pow_pos hm 2) (le_add_of_nonneg_right (sq_nonneg D)) hE)
      (Real.rpow_le_rpow_of_nonpos hρ hA.le (by linarith)) (by positivity) (by positivity)
end ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals
