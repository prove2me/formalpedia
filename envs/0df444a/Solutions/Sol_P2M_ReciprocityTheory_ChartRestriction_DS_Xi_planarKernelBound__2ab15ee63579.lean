-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_planarKernelBound__2ab15ee63579
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:32.188632+00:00
-- url     : https://prove2.me/submissions/766da439-ddbc-48c5-80f9-1694a7f9f871

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PlanarKernelBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RadialKernelIntegrals_lintegral_disc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RadialKernelIntegrals_lintegral_outside
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RadialKernelIntegrals_ker_pointwise

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open RadialKernelIntegrals
namespace ReciprocityTheory.ChartRestriction.DS.Xi
theorem _root_.solution : KER := by
  intro e γ he heγ hγ
  set A : ℝ := 2 * π / (2 - γ) + (4 : ℝ) ^ (-(-1 + e / 2)) * (2 * π / (γ - e)) +
    (6 : ℝ) ^ e * (2 * π / e) with hA
  refine ⟨A / (4 : ℝ) ^ (-(γ - e) / 2), fun c D hD => ?_⟩
  have hS : 0 < ‖c‖ ^ 2 + D ^ 2 := by positivity
  set ρ : ℝ := Real.sqrt (‖c‖ ^ 2 + D ^ 2) / 2 with hρdef
  have hρ : 0 < ρ := div_pos (Real.sqrt_pos.2 hS) two_pos
  have hρ2 : ρ ^ 2 = (‖c‖ ^ 2 + D ^ 2) / 4 := by
    rw [hρdef, div_pow, Real.sq_sqrt hS.le]; norm_num
  have hρc : ‖c‖ ≤ 2 * ρ := by
    have : ‖c‖ ≤ Real.sqrt (‖c‖ ^ 2 + D ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg D])
    rw [hρdef]; linarith
  have hDρ : D ^ 2 = 4 * ρ ^ 2 - ‖c‖ ^ 2 := by rw [hρ2]; ring
  have hS4 : ‖c‖ ^ 2 + D ^ 2 = 4 * ρ ^ 2 := by rw [hρ2]; ring
  have hae : ∀ᵐ x : ℂ, x ≠ 0 ∧ x ≠ c := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ)),
      compl_mem_ae_iff.2 (measure_singleton c)] with x h0 hc
    exact ⟨h0, hc⟩
  refine (lintegral_mono_ae (hae.mono fun x hx =>
    ker_pointwise e γ he heγ hγ c D ρ hρ hρc hDρ x hx.1 hx.2)).trans ?_
  have hm1 : Measurable ((Iic ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-γ)))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Iic
  have hm2 : Measurable ((Ioi ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-(2 + γ - e))))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Ioi
  have hF1 : Measurable fun x : ℂ => ENNReal.ofReal ((ρ ^ 2) ^ (-1 + e / 2)) *
      (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-γ))) ‖x‖ :=
    (hm1.comp measurable_norm).const_mul _
  have hF2 : Measurable fun x : ℂ => ENNReal.ofReal ((4 : ℝ) ^ (-(-1 + e / 2))) *
      (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-(2 + γ - e)))) ‖x‖ :=
    (hm2.comp measurable_norm).const_mul _
  have hF12 : Measurable fun x : ℂ => ENNReal.ofReal ((ρ ^ 2) ^ (-1 + e / 2)) *
      (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-γ))) ‖x‖ +
      ENNReal.ofReal ((4 : ℝ) ^ (-(-1 + e / 2))) *
      (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-(2 + γ - e)))) ‖x‖ := hF1.add hF2
  have h3 : ∫⁻ x : ℂ, (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖x - c‖ =
      ∫⁻ x : ℂ, (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖x‖ :=
    lintegral_sub_right_eq_self
      (fun y : ℂ => (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖y‖) c
  have hI1 : 0 ≤ 2 * π * (ρ ^ (2 - γ) / (2 - γ)) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  have hI2 : 0 ≤ 2 * π * (ρ ^ (2 - (2 + γ - e)) / (2 + γ - e - 2)) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  have hI3 : 0 ≤ 2 * π * ((6 * ρ) ^ (2 - (2 - e)) / (2 - (2 - e))) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  rw [lintegral_add_left hF12, lintegral_add_left hF1,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h3,
    lintegral_disc γ ρ hγ hρ, lintegral_outside (2 + γ - e) ρ (by linarith) hρ,
    lintegral_disc (2 - e) (6 * ρ) (by linarith) (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) hI1) (mul_nonneg (by positivity) hI2),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (by positivity) hI1)
      (mul_nonneg (by positivity) hI2)) (mul_nonneg (by positivity) hI3)]
  apply ENNReal.ofReal_le_ofReal
  have hP1 : (ρ ^ 2) ^ (-1 + e / 2) * ρ ^ (2 - γ) = ρ ^ (e - γ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hρ.le, ← Real.rpow_add hρ]; congr 1; ring
  have hP2 : ρ ^ (2 - (2 + γ - e)) = ρ ^ (e - γ) := by congr 1; ring
  have hP3 : ρ ^ (-γ) * (6 * ρ) ^ e = (6 : ℝ) ^ e * ρ ^ (e - γ) := by
    have h : ρ ^ (-γ) * ρ ^ e = ρ ^ (e - γ) := by rw [← Real.rpow_add hρ]; congr 1; ring
    rw [Real.mul_rpow (by norm_num) hρ.le, ← h]; ring
  have hS' : (‖c‖ ^ 2 + D ^ 2) ^ (-(γ - e) / 2) = (4 : ℝ) ^ (-(γ - e) / 2) * ρ ^ (e - γ) := by
    rw [hS4, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_two,
      ← Real.rpow_mul hρ.le]
    congr 2; ring
  have hne : (4 : ℝ) ^ (-(γ - e) / 2) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  rw [hS', hP2, show (2 : ℝ) + γ - e - 2 = γ - e by ring, show (2 : ℝ) - (2 - e) = e by ring]
  refine le_of_eq ?_
  calc _ = A * ρ ^ (e - γ) := by
        rw [hA]; linear_combination (2 * π / (2 - γ)) * hP1 + (2 * π / e) * hP3
    _ = _ := by field_simp
end ReciprocityTheory.ChartRestriction.DS.Xi
