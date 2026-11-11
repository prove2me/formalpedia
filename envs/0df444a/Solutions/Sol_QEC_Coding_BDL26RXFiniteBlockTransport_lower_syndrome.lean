-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.lower_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:44:34.263803+00:00
-- url     : https://prove2.me/submissions/8d0bd3af-be9a-47a7-884a-a270cd141f6e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_delta
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_map1_eq_remainder
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_map2_injective
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_eq_remainder
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map2_injective
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_delta
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_map2_injective
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
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h X0 a b) =
      (coarseSum S depth i h a b).val := by
  apply map2_injective S depth i h
  have hc := LinearMap.congr_fun (((indexedDecoderData S depth).selectedMap i).commutes_coboundary1)
    (L S depth i h X0 a b)
  change (indexedFamily S depth).coboundary1 i.succ
      (((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h X0 a b)) =
    ((indexedDecoderData S depth).selectedMap i).map2
      ((indexedFamily S depth).coboundary1 i.castSucc (L S depth i h X0 a b)) at hc
  rw [map1_eq_remainder S depth i h X0 Q0 a b he,remainder_delta] at hc
  exact hc.symm
end QEC.Coding.BDL26RXFiniteBlockTransport
