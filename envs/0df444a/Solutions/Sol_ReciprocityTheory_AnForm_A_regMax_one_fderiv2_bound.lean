-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_one_fderiv2_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:35.32093+00:00
-- url     : https://prove2.me/submissions/bb4f1f90-0bef-446a-b5bc-f2716eed6add

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_one_add_one_le_inf
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_eq_conv_sub
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv_conv_eq
import Theorems.Thm_ReciprocityTheory_AnForm_A_norm_bilin_bound
import Theorems.Thm_ReciprocityTheory_AnForm_A_norm_coordMax_sub_le_half
import Theorems.Thm_ReciprocityTheory_AnForm_A_continuous_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_hasCompactSupport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : ∃ C : ℝ, ∀ s : ι → ℝ,
    ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) s‖ ≤ C := by
  set L2 := ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (ι → ℝ)).precompL (ι → ℝ)
  set F := fderiv ℝ (fderiv ℝ (kK : (ι → ℝ) → ℝ))
  have hFc : Continuous F :=
    (kK_contDiff.fderiv_right (m := 1) one_add_one_le_inf).continuous_fderiv (by simp)
  have hFcs : HasCompactSupport F := (kK_hasCompactSupport.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)
  refine ⟨∫ s, ‖L2‖ * ‖F s‖ * (1 / 2), fun s₀ => ?_⟩
  set c := tmax s₀
  set g₀ : (ι → ℝ) → ℝ := fun y => tmax y - c
  have hg₀ : Continuous g₀ := continuous_tmax.sub continuous_const
  have e1 : fderiv ℝ (regMax (ι := ι) 1) =
      convolution (fderiv ℝ kK) g₀ ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (ι → ℝ)) volume := by
    rw [regMax_one_eq_conv_sub c]
    funext x; rw [fderiv_add_const]; exact congrFun (fderiv_conv_eq hg₀) x
  have e2 : fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) s₀ = convolution F g₀ L2 volume s₀ := by
    rw [e1]
    exact ((kK_hasCompactSupport.fderiv (𝕜 := ℝ)).hasFDerivAt_convolution_left _
      (kK_contDiff.fderiv_right (m := 1) one_add_one_le_inf) hg₀.locallyIntegrable s₀).fderiv
  rw [e2, convolution_def]
  refine norm_integral_le_of_norm_le
    (((hFc.norm.integrable_of_hasCompactSupport hFcs.norm).const_mul _).mul_const _)
    (Eventually.of_forall fun s => ?_)
  exact norm_bilin_bound L2 (F s) (g₀ (s₀ - s)) (norm_coordMax_sub_le_half s₀ s)
end ReciprocityTheory.AnForm.A
