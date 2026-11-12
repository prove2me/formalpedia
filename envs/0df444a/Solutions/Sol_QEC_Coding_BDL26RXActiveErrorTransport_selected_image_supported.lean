-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.selected_image_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:17:44.371234+00:00
-- url     : https://prove2.me/submissions/9a46ab9b-b518-4b91-9fd9-98cb3d66a5a1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_localized
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_selected_image_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_selected_image_supported


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
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val) ⊆
      (NZ S depth i h a b).biUnion (zPairImage (rxData S depth i h)) :=
  BDL26RXFiniteBlockTransport.selected_image_supported S depth i h _ _ a b (localized S depth i h a b)
end QEC.Coding.BDL26RXActiveErrorTransport
