-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_semiLocRing_le_empty_1422200f6aab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:06:08.464146+00:00
-- url     : https://prove2.me/submissions/3af4d3d9-1dc5-47df-a921-7095dc1aa5b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingIntClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocFinite

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (𝒲 : Set (Ideal (MRing ι))) : semiLocRing P 𝒲 ≤ semiLocRing P ∅ := by
  unfold semiLocRing
  refine Subring.closure_mono ?_
  rintro _ ⟨u, w, a, hw, -, hu, hwa, rfl⟩
  exact ⟨u, w, a, hw, fun _ h => h.elim, hu, hwa, rfl⟩
end GroundTheory.Heights₂.Heights.Inter
