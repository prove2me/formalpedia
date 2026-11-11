-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.map1_with_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:44:30.829585+00:00
-- url     : https://prove2.me/submissions/806ea821-bc40-485f-a1b9-b5ad6eb8d0a0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_map1_eq_remainder
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_eq_remainder


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXFiniteBlockTransport
theorem _root_.solution (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h X0 a b) =
      updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b) :=
  map1_eq_remainder S depth i h X0 Q0 a b he
end QEC.Coding.BDL26RXFiniteBlockTransport
