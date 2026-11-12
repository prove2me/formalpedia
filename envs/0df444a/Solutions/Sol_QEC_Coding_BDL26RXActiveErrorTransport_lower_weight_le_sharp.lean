-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.lower_weight_le_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:08:33.120262+00:00
-- url     : https://prove2.me/submissions/861cb098-06fd-4c9d-8e33-bce2353f5e96

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_lower_weight_le_neighbors
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_neighbors_card_le_sharp
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXActiveErrorTransport
theorem _root_.solution (a b : Upper S depth i) :
    HammingWeight (L S depth i h a b) ≤ (activeQ S depth i h (a+b)).card +
      ∑ x ∈ activeX S depth i h (a+b), (incidentQ S depth i x).card :=
  (lower_weight_le_neighbors S depth i h a b).trans (neighbors_card_le_sharp S depth i h a b)
end QEC.Coding.BDL26RXActiveErrorTransport
