-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.remainder_q_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:14:48.576031+00:00
-- url     : https://prove2.me/submissions/4e083113-8e71-435a-ba20-acb486b7f403

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_delta
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_actual_coboundary1
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map2_q_zero
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_delta
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_x_zero
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    (q : QCoord S i) (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    (rxContract S depth i h).rx_local_complexes.cqDelta1 q
      (restrictWordLinear ((rxLq S depth i h).correctionRegion q) (R S depth i h X0 a b))=0 := by
  have hk := (rxContract S depth i h).support_decomposition.cqDelta1_restriction_global q
    (R S depth i h X0 a b) (fun y => remainder_x_zero S depth i h X0 Q0 y a b he)
  rw [actual_coboundary1 S depth,remainder_delta,map2_q_zero] at hk
  exact hk.symm
end QEC.Coding.BDL26RXFiniteBlockTransport
