-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementSupport.rxCq_exists_global_outgoing_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:02:56.07456+00:00
-- url     : https://prove2.me/submissions/14d95d91-1c90-4490-8f2f-4cef6fb1baaf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxQOutgoing_sum_weight
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCq_exists_local_weight_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical
namespace QEC.Coding.BDL26ReplacementSupport
theorem _root_.solution
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (syndrome : Word Field (QDoubleCylinderEdge P q S))
    (hs : syndrome ∈ LinearMap.range
      (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S))) :
    ∃ correction : Word Field (QDoubleCylinderVertex P q S),
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) correction = syndrome ∧
        (∑ z : P.Z, HammingWeight (rxQOutgoing P q S correction z)) ≤
          HammingWeight syndrome := by
  obtain ⟨correction, hboundary, hweight⟩ := rxCq_exists_local_weight_le P q S syndrome hs
  refine ⟨correction, hboundary, ?_⟩
  rw [rxQOutgoing_sum_weight]
  exact hweight
end QEC.Coding.BDL26ReplacementSupport
