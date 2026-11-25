-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv2_sub_of_contDiffOn_acec6951921d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:57.285154+00:00
-- url     : https://prove2.me/submissions/d91aa5e0-1cfa-4286-9295-129ca9ee5640

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


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax regMax_contDiff regMax_add_const abs_regMax_le regMax_fderiv_sum
  regMax_fderiv_nonneg fderiv2_regMax regMax_one_fderiv2_bound regMax_comp_fderiv2 two_le_inf)
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {U : Set E} (hU : IsOpen U) {φ ψ : E → ℝ}
    (hφ : ContDiffOn ℝ 2 φ U) (hψ : ContDiffOn ℝ 2 ψ U) {x : E} (hx : x ∈ U) :
    fderiv ℝ (fderiv ℝ fun y => φ y - ψ y) x =
      fderiv ℝ (fderiv ℝ φ) x - fderiv ℝ (fderiv ℝ ψ) x := by
  have h : fderiv ℝ (fun y => φ y - ψ y) =ᶠ[𝓝 x] fun y => fderiv ℝ φ y - fderiv ℝ ψ y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_sub ((hφ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      ((hψ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  rw [h.fderiv_eq]
  exact fderiv_sub
    (((hφ.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num))
    (((hψ.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num))
end GroundTheory.Heights₂.Heights.AnalyticLimit
