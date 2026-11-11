-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.two_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:31:12.412662+00:00
-- url     : https://prove2.me/submissions/e7bb6782-e09b-4a00-8948-f45bcaa893b8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_with_potential
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_coarse_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_with_potential


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
theorem _root_.solution (x : XCoord S i) (a b : Upper S depth i) (he : OneX S depth i h x a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h x a b) =
        updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (potential S depth i h x a b) ∧
      (indexedFamily S depth).coboundary1 i.castSucc (lowerWord S depth i h x a b) =
        (coarseSum S depth i h a b).val ∧
      hammingSupport (potential S depth i h x a b) ⊆ degreeZeroBlock S depth i h x ∧
      hammingSupport (lowerWord S depth i h x a b) ⊆ incidentQ S depth i x ∧
      hammingSupport (coarseSum S depth i h a b).val ⊆ incidentZ S depth i x :=
  ⟨map1_with_potential S depth i h x a b he,lower_syndrome S depth i h x a b he,
    potential_supported S depth i h x a b,lower_supported S depth i h x a b he,
    coarse_supported S depth i h x a b he⟩
end QEC.Coding.BDL26RXXStarTransport
