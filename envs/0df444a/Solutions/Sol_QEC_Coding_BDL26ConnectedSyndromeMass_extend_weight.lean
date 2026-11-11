-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.extend_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:04:40.122265+00:00
-- url     : https://prove2.me/submissions/4916a9c9-ca25-4673-83a9-928edd5da0ca

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_fiberExtend_weight


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
theorem _root_.solution (S : OddScale) (i : ℕ) (u : GraphVertex S i)
    (x : Word Bit (OwnerFiber S i u)) : HammingWeight (extend S i u x)=HammingWeight x := by
  convert fiberExtend_weight (owner S i) u x using 1 <;> congr 1
  exact Subsingleton.elim _ _
end QEC.Coding.BDL26ConnectedSyndromeMass
