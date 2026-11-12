-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.x_pieces_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:42:22.713705+00:00
-- url     : https://prove2.me/submissions/6ee15e85-babd-45c5-8fd2-655a5c99d043

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_x_regions_disjoint

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
theorem _root_.solution (E : Upper S depth i) (x y : XCoord S i) (hn : x≠y) :
    Disjoint (xPiece S depth i h E x) (xPiece S depth i h E y) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (Finset.disjoint_left.mp (x_regions_disjoint S depth i h x y hn))
    (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hq).1
end QEC.Coding.BDL26RXActiveErrorTransport
