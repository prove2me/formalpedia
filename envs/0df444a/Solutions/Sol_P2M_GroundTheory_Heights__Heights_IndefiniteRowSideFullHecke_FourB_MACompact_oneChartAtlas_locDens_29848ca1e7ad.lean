-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_locDens_29848ca1e7ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:55:07.576226+00:00
-- url     : https://prove2.me/submissions/37573aac-872f-4cbf-b42a-82747cf4f9a8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OneChartAtlasIndexEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_maDens_eq_topDens_8f56fb96d4ed
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
theorem _root_.solution (hΩ : IsOpen Ω) [Nonempty Ω] (L : LocPot Ω) (ψ : (Fin D → ℂ) → ℝ)
    (hL : ∀ x x', L.φ x x' = ψ x' / 2) (y : Fin D → ℂ) (hy : y ∈ Ω) :
    locDens (oneChartAtlas hΩ) (fun _ => L) (j0 hΩ) y = topDens ψ y := by
  unfold locDens
  simp only [hL]
  apply maDens_eq_topDens
  filter_upwards [hΩ.mem_nhds hy] with z hz
  show ψ ((inclChart hΩ).symm z : Fin D → ℂ) / 2 = ψ z / 2
  rw [inclChart_symm hΩ z hz]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
