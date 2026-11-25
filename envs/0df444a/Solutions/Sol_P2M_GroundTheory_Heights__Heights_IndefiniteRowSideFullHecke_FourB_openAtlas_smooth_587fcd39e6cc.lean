-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_smooth_587fcd39e6cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:50:38.370282+00:00
-- url     : https://prove2.me/submissions/f6f31494-90d2-46cb-8eaf-bfb9c18f387a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OpenAtlasSymmEventuallyEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_symm_eventuallyEq_56d36dcbd8e2
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
theorem _root_.solution {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω)
    (F : (Fin D → ℂ) → ℝ) (hF : ContDiffOn ℝ ∞ F Ω) :
    (openAtlas Ω hΩ).Smooth fun x => F x := by
  intro j
  have hsub : ((openAtlas Ω hΩ).chart j).target ∩ ((openAtlas Ω hΩ).chart j).symm ⁻¹' Set.univ ⊆
      (Ω : Set (Fin D → ℂ)) := by
    intro y hy
    have h := hy.1
    change y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target at h
    simpa using h
  exact (hF.mono hsub).congr fun y hy =>
    (openAtlas_symm_eventuallyEq Ω hΩ j F (hsub hy)).eq_of_nhds
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
