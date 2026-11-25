-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_smooth_671d5e416723
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:50:34.089527+00:00
-- url     : https://prove2.me/submissions/85cfad48-edc2-45b4-821a-62cbff5c5544

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OneChartAtlasIndexEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_inclChart_symm_08c35d356223
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
theorem _root_.solution (hΩ : IsOpen Ω) [Nonempty Ω] {f : (Fin D → ℂ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) : (oneChartAtlas hΩ).Smooth (fun x : Ω => f x) := by
  intro j
  have hs : (inclChart hΩ).target ∩ (inclChart hΩ).symm ⁻¹' Set.univ = Ω := by
    simp [inclChart_target]
  show ContDiffOn ℝ ∞ ((fun x : Ω => f x) ∘ (inclChart hΩ).symm)
    ((inclChart hΩ).target ∩ (inclChart hΩ).symm ⁻¹' Set.univ)
  rw [hs]
  exact hf.congr fun y hy => by simp only [Function.comp_apply, inclChart_symm hΩ y hy]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
