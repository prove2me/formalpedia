-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.ownerFiber_rz_x_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:09:58.050851+00:00
-- url     : https://prove2.me/submissions/b345fe59-54e9-44a4-835c-df3ae50dff52

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
    (x : (state S (n+1)).presentation.X) : IsEmpty (OwnerFiber S (n+2) (Vertex.x x)) := by
  refine ⟨?_⟩
  rintro ⟨c,hc⟩
  rw [owner_rz_apply S n h c] at hc
  cases hc
end QEC.Coding.BDL26ConnectedSyndromeMass
