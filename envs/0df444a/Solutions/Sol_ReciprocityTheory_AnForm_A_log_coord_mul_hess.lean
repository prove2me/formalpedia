-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.log_coord_mul_hess
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:34.445007+00:00
-- url     : https://prove2.me/submissions/576b1584-221b-493b-8708-027a8617069e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_log_coord_mul
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_log_coord_mul_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Laplacian Pointwise
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (j : Fin (D + 1)) {u : (Fin (D + 1) → ℂ) → ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasCompactSupport u) (v w : Fin (D + 1) → ℂ)
    (h : v j = 0 ∨ w j = 0) :
    Integrable (fun z => Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z v w) ∧
      ∫ z, Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z v w = 0 := by
  have hu1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hH : Continuous (fderiv ℝ (fderiv ℝ u)) := hu1.continuous_fderiv one_ne_zero
  refine ⟨integrable_log_coord_mul j ((hH.clm_apply continuous_const).clm_apply continuous_const)
    (((hs.fderiv ℝ).fderiv_apply ℝ v).comp_left
      (g := fun L : (Fin (D + 1) → ℂ) →L[ℝ] ℝ => L w) (by simp)), ?_⟩
  have key : ∀ v w : Fin (D + 1) → ℂ, v j = 0 →
      ∫ z, Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z v w = 0 := by
    intro v w hv
    have hg : ContDiff ℝ 1 (fun z => fderiv ℝ u z w) := hu1.clm_apply contDiff_const
    have hgs : HasCompactSupport (fun z => fderiv ℝ u z w) := hs.fderiv_apply ℝ w
    rw [← integral_log_coord_mul_fderiv j hg hgs hv]
    congr 1; funext z; congr 1
    rw [fderiv_clm_apply ((hu1.differentiable one_ne_zero) z) (differentiableAt_const w)]
    simp
  rcases h with hv | hw
  · exact key v w hv
  · have hsym : ∀ z, fderiv ℝ (fderiv ℝ u) z v w = fderiv ℝ (fderiv ℝ u) z w v :=
      fun z => (hu.contDiffAt.isSymmSndFDerivAt (by simp)) v w
    simp_rw [hsym]
    exact key w v hw
end ReciprocityTheory.AnForm.A
