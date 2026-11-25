-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_deriv_deriv_line_c0b6722991ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:57:27.608685+00:00
-- url     : https://prove2.me/submissions/3d97cec7-8ae4-4c4e-b2fd-443beb8c6f8f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegularizedCurvature
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
theorem _root_.solution {f : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (e : J → ℂ) :
    deriv (deriv fun s : ℝ => f (z + s • e)) 0 = fderiv ℝ (fderiv ℝ f) z e e := by
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => z + s • e) e s := fun s =>
    (((hasDerivAt_id s).smul_const e).const_add z).congr_deriv (one_smul ℝ e)
  have hz0 : z + (0 : ℝ) • e = z := by rw [zero_smul, add_zero]
  have hcont : Tendsto (fun s : ℝ => z + s • e) (𝓝 0) (𝓝 z) := by
    have h := (hline 0).continuousAt.tendsto
    rwa [hz0] at h
  have hfe : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hev : deriv (fun s : ℝ => f (z + s • e)) =ᶠ[𝓝 0] fun s => fderiv ℝ f (z + s • e) e := by
    filter_upwards [hcont.eventually hfe] with s hs
    have h := (hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hline s)
    exact h.deriv
  have hH : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hA : HasFDerivAt (fun y => fderiv ℝ f y e) ((fderiv ℝ (fderiv ℝ f) z).flip e) z := by
    have h := hH.clm_apply (hasFDerivAt_const e z)
    simpa using h
  have hd : HasDerivAt (fun s : ℝ => fderiv ℝ f (z + s • e) e) (fderiv ℝ (fderiv ℝ f) z e e) 0 :=
    hA.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) hz0.symm
  rw [hev.deriv_eq]
  exact hd.deriv
end GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
