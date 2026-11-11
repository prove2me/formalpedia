-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.error_other_x_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:04:53.584941+00:00
-- url     : https://prove2.me/submissions/57bbd931-bd7b-47fb-98e0-da77f0d71444

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_zero_off_support

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
theorem _root_.solution (x y : XCoord S i) (hy : y≠x)
    (e : Upper S depth i)
    (he : hammingSupport e ⊆ (rxLx S depth i h).correctionRegion x) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) e=0 := by
  funext p
  apply zero_off_support e _ he p.val
  intro hp
  exact (Finset.disjoint_left.mp
    ((rxData S depth i h).cx_correction_regions_pairwise_disjoint y x hy)) p.property hp
end QEC.Coding.BDL26RXXStarTransport
