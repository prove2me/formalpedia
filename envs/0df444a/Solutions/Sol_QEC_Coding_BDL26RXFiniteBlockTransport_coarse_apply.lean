-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.coarse_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:49:05.637008+00:00
-- url     : https://prove2.me/submissions/2c4c2aff-9c44-4b0a-8a16-bfe8c2c6a603

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_zero_off_support
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
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) (z : ZCoord S i) :
    (coarseSum S depth i h a b).val z =
      ∑ q ∈ neighbors S depth i X0 Q0, L S depth i h X0 a b q *
        (if (state S i.val).presentation.qz q z=true then 1 else 0) := by
  rw [← lower_syndrome S depth i h X0 Q0 a b he,indexedFamily_coboundary1]
  change (∑ q, L S depth i h X0 a b q *
    (if (state S i.val).presentation.qz q z=true then 1 else 0)) = _
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro q _ hq
  rw [zero_off_support _ _ (lower_supported S depth i h X0 Q0 a b he) q hq,zero_mul]
end QEC.Coding.BDL26RXFiniteBlockTransport
