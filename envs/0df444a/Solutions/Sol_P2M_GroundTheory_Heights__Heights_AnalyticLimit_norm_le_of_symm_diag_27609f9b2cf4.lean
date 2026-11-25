-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_norm_le_of_symm_diag_27609f9b2cf4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:34:13.14879+00:00
-- url     : https://prove2.me/submissions/f0423037-3290-4064-a250-4f565debfb1f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Theorems.Thm_ReciprocityTheory_AnForm_A_abs_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv2_regMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_add_const
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_comp_fderiv2
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_sum
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_fderiv2_bound
import Theorems.Thm_ReciprocityTheory_AnForm_A_two_le_inf
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax regMax_contDiff regMax_add_const abs_regMax_le regMax_fderiv_sum
  regMax_fderiv_nonneg fderiv2_regMax regMax_one_fderiv2_bound regMax_comp_fderiv2 two_le_inf)
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {H : E →L[ℝ] E →L[ℝ] ℝ} (hs : ∀ v w, H v w = H w v) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : ∀ v, |H v v| ≤ c * ‖v‖ ^ 2) : ‖H‖ ≤ 2 * c := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun x y => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have ha : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hb : 0 < ‖y‖ := norm_pos_iff.2 hy
  set x' := ‖x‖⁻¹ • x
  set y' := ‖y‖⁻¹ • y
  have hx' : ‖x'‖ = 1 := by simp [x', norm_smul, ha.ne']
  have hy' : ‖y'‖ = 1 := by simp [y', norm_smul, hb.ne']
  have hxy : H x y = ‖x‖ * ‖y‖ * H x' y' := by
    simp only [x', y', map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  have key : 4 * H x' y' = H (x' + y') (x' + y') - H (x' - y') (x' - y') := by
    simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    rw [hs y' x']
    ring
  have h1 : ‖x' + y'‖ ^ 2 ≤ 4 := by
    have := norm_add_le x' y'
    rw [hx', hy'] at this
    nlinarith [norm_nonneg (x' + y')]
  have h2 : ‖x' - y'‖ ^ 2 ≤ 4 := by
    have := norm_sub_le x' y'
    rw [hx', hy'] at this
    nlinarith [norm_nonneg (x' - y')]
  have k1 := hc (x' + y')
  have k2 := hc (x' - y')
  have s1 : c * ‖x' + y'‖ ^ 2 ≤ c * 4 := mul_le_mul_of_nonneg_left h1 hc0
  have s2 : c * ‖x' - y'‖ ^ 2 ≤ c * 4 := mul_le_mul_of_nonneg_left h2 hc0
  have hH : |H x' y'| ≤ 2 * c := by
    rw [abs_le] at k1 k2 ⊢
    constructor <;> linarith
  rw [Real.norm_eq_abs, hxy, abs_mul, abs_mul, abs_norm, abs_norm]
  have hab : 0 ≤ ‖x‖ * ‖y‖ := by positivity
  calc ‖x‖ * ‖y‖ * |H x' y'| ≤ ‖x‖ * ‖y‖ * (2 * c) := mul_le_mul_of_nonneg_left hH hab
    _ = 2 * c * ‖x‖ * ‖y‖ := by ring
end GroundTheory.Heights₂.Heights.AnalyticLimit
