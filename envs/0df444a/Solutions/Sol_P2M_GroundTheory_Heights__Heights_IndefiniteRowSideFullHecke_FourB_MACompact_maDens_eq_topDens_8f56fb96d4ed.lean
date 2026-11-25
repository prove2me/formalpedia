-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_maDens_eq_topDens_8f56fb96d4ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:57.737215+00:00
-- url     : https://prove2.me/submissions/cbdc99b1-030f-484e-a05d-7d9d052b3916

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OneChartAtlasIndexEq
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
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
variable {D : ℕ} {Ω : Set (Fin D → ℂ)}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
theorem _root_.solution (f ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (h : f =ᶠ[𝓝 z] fun y => ψ y / 2) : maDens (fun _ : Fin D => f) z = topDens ψ z := by
  have h2 : fderiv ℝ (fderiv ℝ f) z = fderiv ℝ (fderiv ℝ fun y => ψ y / 2) z :=
    h.fderiv.fderiv_eq
  have h3 : hessC f z = cxHessian (fun y => ψ y / 2) z := by
    unfold hessC cxHessian
    rw [h2]
  simp only [maDens, topDens, maDensity, mdisc, mixedDisc, h3]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
