-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.ownerFiber_rz_q_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:10:00.811448+00:00
-- url     : https://prove2.me/submissions/347d3bff-55b8-4c68-98e4-163ff5c8d05b

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSyndromeMass
open Classical BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26BoundedValence
open BDL26LocalSyndromeWeights BDL26ReplacementSupport MultiscaleDecoder
open scoped BigOperators Classical
universe u
namespace QEC.Coding.BDL26ConnectedSyndromeMass
theorem _root_.solution (S : OddScale) (n : ℕ) (h : (n+2)%2≠1)
    (q : (state S (n+1)).presentation.Q) : IsEmpty (OwnerFiber S (n+2) (Vertex.q q)) := by
  refine ⟨?_⟩
  rintro ⟨c,hc⟩
  rw [owner_rz_apply S n h c] at hc
  cases hc
end QEC.Coding.BDL26ConnectedSyndromeMass
