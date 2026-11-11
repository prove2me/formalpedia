-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.lower_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:05:23.96332+00:00
-- url     : https://prove2.me/submissions/2eba4bfc-6d51-4a12-b371-9ea63836c5b0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_delta
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_eq_remainder
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map2_injective
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_map2_injective
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_map2_injective
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
theorem _root_.solution (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    (indexedFamily S depth).coboundary1 i.castSucc (lowerWord S depth i h x a b) =
      (coarseSum S depth i h a b).val := by
  apply map2_injective S depth i h
  have hc := LinearMap.congr_fun (((indexedDecoderData S depth).selectedMap i).commutes_coboundary1)
    (lowerWord S depth i h x a b)
  change (indexedFamily S depth).coboundary1 i.succ
      (((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h x a b)) =
    ((indexedDecoderData S depth).selectedMap i).map2
      ((indexedFamily S depth).coboundary1 i.castSucc (lowerWord S depth i h x a b)) at hc
  rw [map1_eq_remainder S depth i h x a b he,remainder_delta] at hc
  exact hc.symm
end QEC.Coding.BDL26RXXStarTransport
