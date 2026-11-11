-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.x_q_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:27:18.302922+00:00
-- url     : https://prove2.me/submissions/1c047013-c137-4a8a-ab5c-d87e5ee8e7ed

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_correction_sectors_disjoint


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
theorem _root_.solution (x : XCoord S i) (q : QCoord S i) :
    Disjoint ((rxLx S depth i h).correctionRegion x)
      ((rxLq S depth i h).correctionRegion q) := by
  apply Finset.disjoint_left.mpr
  intro p hpx hpq
  apply (Finset.disjoint_left.mp (rxData S depth i h).correction_sectors_disjoint)
  · exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,hpx⟩
  · rw [(rxData S depth i h).qCorrectionSector_eq_regions]
    exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,hpq⟩
end QEC.Coding.BDL26RXXStarTransport
