-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.localPotential_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:54:25.103372+00:00
-- url     : https://prove2.me/submissions/7c93b6a8-d32c-4997-a242-44a0474e0517

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport

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
theorem _root_.solution (x : XCoord S i) (a b : Upper S depth i) :
    (rxContract S depth i h).rx_local_complexes.cxDelta0 x (localPotential S depth i h x a b) =
      restrictWordLinear ((rxLx S depth i h).correctionRegion x) (updated S depth i h a b) := by
  unfold localPotential
  split_ifs with hz
  · rw [map_zero,hz]
  · exact Classical.choose_spec (localPotential_exists S depth i h x a b)
end QEC.Coding.BDL26RXXStarTransport
