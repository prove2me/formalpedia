-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_topDens_continuousOn_f7eedd4e6ecd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:50:14.793253+00:00
-- url     : https://prove2.me/submissions/fbb011df-666b-477f-9e39-d7a3d43e8562

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OneChartAtlasIndexEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_maDens_eq_topDens_8f56fb96d4ed
import Theorems.Thm_ReciprocityTheory_AnForm_M_maDens_continuousOn


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
theorem _root_.solution {ψ : (Fin D → ℂ) → ℝ} (hΩ : IsOpen Ω) (hψ : ContDiffOn ℝ ∞ ψ Ω) :
    ContinuousOn (topDens ψ) Ω := by
  have e : topDens ψ = maDens (fun _ : Fin D => fun y => ψ y / 2) :=
    funext fun z => (maDens_eq_topDens _ ψ z EventuallyEq.rfl).symm
  rw [e]
  exact maDens_continuousOn _ Ω hΩ fun _ => (hψ.div_const 2).of_le (WithTop.coe_le_coe.2 le_top)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
