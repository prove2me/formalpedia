-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.active_piece_unions_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:42:29.203422+00:00
-- url     : https://prove2.me/submissions/3a1c496c-8d99-4875-b99e-af3ef80971a5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_x_q_regions_disjoint

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
theorem _root_.solution (E : Upper S depth i) :
    Disjoint ((activeX S depth i h E).biUnion (xPiece S depth i h E))
      ((activeQ S depth i h E).biUnion (qPiece S depth i h E)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨x,_,hpx⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨q,_,hpq⟩ := Finset.mem_biUnion.mp hq
  exact (Finset.disjoint_left.mp (x_q_regions_disjoint S depth i h x q))
    (Finset.mem_inter.mp hpx).1 (Finset.mem_inter.mp hpq).1
end QEC.Coding.BDL26RXActiveErrorTransport
