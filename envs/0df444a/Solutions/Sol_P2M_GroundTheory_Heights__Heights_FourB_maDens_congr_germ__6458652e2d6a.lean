-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_maDens_congr_germ__6458652e2d6a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:07.49682+00:00
-- url     : https://prove2.me/submissions/d7dd6529-8de3-4587-b7b6-a3ea30ab389c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_HypImp
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OfFubiniStudyCoverMass
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
open OpenSetChart
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 y] ψ i) : maDens φ y = maDens ψ y := by
  have hH : ∀ i, hessC (φ i) y = hessC (ψ i) y := by
    intro i
    have h1 : fderiv ℝ (φ i) =ᶠ[𝓝 y] fderiv ℝ (ψ i) := (h i).fderiv
    unfold hessC
    rw [h1.fderiv_eq]
  unfold maDens
  simp only [hH]
end GroundTheory.Heights₂.Heights.FourB
