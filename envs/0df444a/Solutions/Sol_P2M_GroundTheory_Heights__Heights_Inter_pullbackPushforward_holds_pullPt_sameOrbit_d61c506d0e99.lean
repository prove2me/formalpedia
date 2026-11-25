-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_pullPt_sameOrbit_d61c506d0e99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:38.167203+00:00
-- url     : https://prove2.me/submissions/3d7ba5c8-386f-46f5-97d5-7e45d8ac30b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullBad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_HasStrictFDerivAtEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_sameOrbit_comp_b367633ae983

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set
open GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
namespace GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
theorem _root_.solution (hv : IsBlockMap κ v) {x z : R.X} (hz : z ∈ R.U x) :
    SameOrbit (pullPt R v z) (fun p => R.lift x z (v p)) :=
  sameOrbit_comp hv (R.compat z x z ⟨R.mem_U z, hz⟩)
end GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
