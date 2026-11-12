-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.q_pieces_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:42:25.759202+00:00
-- url     : https://prove2.me/submissions/b9310542-b545-4a08-9f7c-181c7a18151a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_q_regions_disjoint

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
theorem _root_.solution (E : Upper S depth i) (q r : QCoord S i) (hn : q≠r) :
    Disjoint (qPiece S depth i h E q) (qPiece S depth i h E r) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (Finset.disjoint_left.mp (q_regions_disjoint S depth i h q r hn))
    (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hq).1
end QEC.Coding.BDL26RXActiveErrorTransport
