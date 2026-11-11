-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.selected_rx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:25:38.422622+00:00
-- url     : https://prove2.me/submissions/f636f418-257c-4b08-b69c-d11dacfc9674

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXXStarTransport
theorem _root_.solution :
    (indexedDecoderData S depth).selectedMap i = (indexedDecoderData S depth).rxMap i := by
  rw [selectedMap_eq]
  rfl
end QEC.Coding.BDL26RXXStarTransport
