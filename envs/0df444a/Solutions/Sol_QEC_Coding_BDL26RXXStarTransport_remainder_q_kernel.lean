-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.remainder_q_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:34:28.781206+00:00
-- url     : https://prove2.me/submissions/5909625c-db1b-4ffb-af80-7403cc6968d9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_delta
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_actual_coboundary1
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map2_q_zero
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution (x : XCoord S i) (q : QCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    (rxContract S depth i h).rx_local_complexes.cqDelta1 q
      (restrictWordLinear ((rxLq S depth i h).correctionRegion q) (remainder S depth i h x a b))=0 := by
  have hk := (rxContract S depth i h).support_decomposition.cqDelta1_restriction_global q
    (remainder S depth i h x a b) (fun y => remainder_x_zero S depth i h x y a b he)
  rw [actual_coboundary1 S depth,remainder_delta,map2_q_zero] at hk
  exact hk.symm
end QEC.Coding.BDL26RXXStarTransport
