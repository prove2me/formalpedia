-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_laplacian_line_eq_levi_3ac6aef88d61
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:54.471842+00:00
-- url     : https://prove2.me/submissions/353c5115-b070-428e-ae04-b8e53faa1284

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemiPosTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_ReciprocityTheory_AnForm_A_leviOne
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
open GroundTheory.Heights₂.Heights.Inter.SemipositiveTwist
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.Inter.SemipositiveTwist
theorem _root_.solution {φ : (J → ℂ) → ℝ} {z : J → ℂ} (hφ : ContDiffAt ℝ 2 φ z) (v : J → ℂ) :
    Δ (fun t : ℂ => φ (z + t • v)) 0 = 4 * ReciprocityTheory.AnForm.levi φ z v := by
  have h1 : ReciprocityTheory.AnForm.levi (fun w : Fin 1 → ℂ => φ (z + w 0 • v)) (fun _ => 0) (Pi.single 0 1) =
      Δ (fun t : ℂ => φ (z + t • v)) 0 / 4 :=
    ReciprocityTheory.AnForm.A.leviOne (fun t : ℂ => φ (z + t • v)) 0
  set L : (Fin 1 → ℂ) →L[ℂ] (J → ℂ) :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight v with hL
  have hτ : AnalyticAt ℂ (fun w => z + L w) (fun _ => 0) :=
    analyticAt_const.add (L.analyticAt _)
  have hτ0 : z + L (fun _ => (0 : ℂ)) = z := by
    simp [hL]
  have hcomp : (fun w : Fin 1 → ℂ => φ (z + w 0 • v)) = φ ∘ fun w => z + L w := by
    funext w
    simp [hL]
  have hD : fderiv ℂ (fun w => z + L w) (fun _ => 0) (Pi.single 0 1) = v := by
    rw [((L.hasFDerivAt).const_add z).fderiv]
    simp [hL]
  have hφ' : ContDiffAt ℝ 2 φ (z + L (fun _ => 0)) := by
    rw [hτ0]
    exact hφ
  rw [hcomp, ReciprocityTheory.AnForm.levi_comp _ hτ hφ', hτ0, hD] at h1
  linarith
end GroundTheory.Heights₂.Heights.Inter.SemipositiveTwist
