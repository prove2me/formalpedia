-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.boundaryGradient_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:43:44.882548+00:00
-- url     : https://prove2.me/submissions/095271e2-b5bc-4042-b8ce-5886c63dfde5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry

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
theorem _root_.solution (x : XCoord S i) :
    (rxContract S depth i h).rx_local_complexes.cxDelta1 x
      (boundaryGradient S depth i h x)=0 := by
  have hm : boundaryGradient S depth i h x ∈
      LinearMap.range ((rxContract S depth i h).rx_local_complexes.cxDelta0 x) :=
    ⟨boundarySingleton S depth i x,rfl⟩
  rw [← (rxContract S depth i h).rx_local_cohomology.cx_h1_ker_eq_range x] at hm
  exact hm
end QEC.Coding.BDL26RXXStarTransport
