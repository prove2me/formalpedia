-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_le_of_le_fa7336628a43
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:22.210299+00:00
-- url     : https://prove2.me/submissions/b1d7b280-77d3-4746-834b-4cd7037566e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegularizedCurvature
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_sndDeriv_nonneg_of_isLocalMin_18eb058d37e7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
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
theorem _root_.solution {φ ψ : (J → ℂ) → ℝ} {z : J → ℂ} (hφ : ContDiffAt ℝ 2 φ z) (hψ : ContDiffAt ℝ 2 ψ z)
    (hle : ∀ᶠ y in 𝓝 z, ψ y ≤ φ y) (heq : ψ z = φ z) (w : J → ℂ) :
    ReciprocityTheory.AnForm.levi ψ z w ≤ ReciprocityTheory.AnForm.levi φ z w := by
  have hf : ContDiffAt ℝ 2 (fun y => φ y + (-1) * ψ y) z := hφ.add (contDiffAt_const.mul hψ)
  have hmin : IsLocalMin (fun y => φ y + (-1) * ψ y) z := by
    filter_upwards [hle] with y hy
    simp only [heq]
    linarith
  have h1 := sndDeriv_nonneg_of_isLocalMin hf hmin w
  have h2 := sndDeriv_nonneg_of_isLocalMin hf hmin (Complex.I • w)
  have h3 : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => φ y + (-1) * ψ y) z w := by
    unfold ReciprocityTheory.AnForm.levi
    exact div_nonneg (add_nonneg h1 h2) (by norm_num)
  rw [ReciprocityTheory.AnForm.levi_add_smul (-1) hφ hψ w] at h3
  linarith
end GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
