-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.map1_with_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:04:08.74814+00:00
-- url     : https://prove2.me/submissions/3acb11d9-4ea4-4abe-a224-592005f28058

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_localized
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_map1_with_potential
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_with_potential
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_with_potential


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
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h a b) =
      updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h a b) :=
  BDL26RXFiniteBlockTransport.map1_with_potential S depth i h _ _ a b (localized S depth i h a b)
end QEC.Coding.BDL26RXActiveErrorTransport
