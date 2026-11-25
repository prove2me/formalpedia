-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_topDens_congr_a0b8135a3cf1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:30.79382+00:00
-- url     : https://prove2.me/submissions/36aa7eac-6dda-44b4-8ca1-075803da3d84

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OneChartAtlasIndexEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_maDens_eq_topDens_8f56fb96d4ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
variable {D : ℕ} {Ω : Set (Fin D → ℂ)}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
theorem _root_.solution {ψ ψ' : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (h : ψ =ᶠ[𝓝 z] ψ') :
    topDens ψ z = topDens ψ' z := by
  have h1 : (fun y => ψ y / 2) =ᶠ[𝓝 z] fun y => ψ' y / 2 := h.fun_comp (· / 2)
  exact (maDens_eq_topDens _ ψ z EventuallyEq.rfl).symm.trans (maDens_eq_topDens _ ψ' z h1)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
