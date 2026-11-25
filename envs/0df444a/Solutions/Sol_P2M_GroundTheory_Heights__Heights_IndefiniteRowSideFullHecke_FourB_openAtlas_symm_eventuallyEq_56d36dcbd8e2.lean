-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_symm_eventuallyEq_56d36dcbd8e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:53.9552+00:00
-- url     : https://prove2.me/submissions/52f9da87-0bd4-4700-8982-eb076e7152f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OpenAtlasSymmEventuallyEq
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
theorem _root_.solution {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ))
    (hΩ : Nonempty Ω) (j : Fin (openAtlas Ω hΩ).n) (F : (Fin D → ℂ) → ℝ) {y : Fin D → ℂ}
    (hy : y ∈ Ω) :
    (fun z => F (((openAtlas Ω hΩ).chart j).symm z : Fin D → ℂ)) =ᶠ[𝓝 y] F := by
  have hy' : y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target := by simpa using hy
  filter_upwards [(Ω.openPartialHomeomorphSubtypeCoe hΩ).open_target.mem_nhds hy'] with z hz
  have h := (Ω.openPartialHomeomorphSubtypeCoe hΩ).right_inv hz
  simp only [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] at h
  change F ((Ω.openPartialHomeomorphSubtypeCoe hΩ).symm z : Fin D → ℂ) = F z
  rw [h]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
