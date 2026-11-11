-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.coarse_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:15:10.165034+00:00
-- url     : https://prove2.me/submissions/dab38e4c-5c24-40c4-b6e6-3f4cbac52fd0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_zero_off_support
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
    (he : OneX S depth i h x a b) (z : ZCoord S i) :
    (coarseSum S depth i h a b).val z =
      ∑ q ∈ incidentQ S depth i x, lowerWord S depth i h x a b q *
        (if (state S i.val).presentation.qz q z=true then 1 else 0) := by
  rw [← lower_syndrome S depth i h x a b he,indexedFamily_coboundary1]
  change (∑ q, lowerWord S depth i h x a b q *
    (if (state S i.val).presentation.qz q z=true then 1 else 0)) = _
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro q _ hq
  rw [zero_off_support _ _ (lower_supported S depth i h x a b he) q hq,zero_mul]
end QEC.Coding.BDL26RXXStarTransport
