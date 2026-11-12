-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.selected_image_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:17:47.627286+00:00
-- url     : https://prove2.me/submissions/6ef0420c-a9d7-4806-afee-d444b572fabc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_selected_image_pair
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_selected_image_pair
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_selected_image_pair


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
theorem _root_.solution (a b : Upper S depth i) (z : ZCoord S i) (copy : Fin 2) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val
      ((rxData S depth i h).induced.zPairEquiv (z,copy)).val=(coarseSum S depth i h a b).val z :=
  BDL26RXFiniteBlockTransport.selected_image_pair S depth i h a b z copy
end QEC.Coding.BDL26RXActiveErrorTransport
