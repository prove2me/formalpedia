-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_cq_total_boundary_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:31:47.997097+00:00
-- url     : https://prove2.me/submissions/dd06c5eb-31ba-49be-a8ae-e4d1e5e60eed

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_cq_boundary_zero

set_option autoImplicit false
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
open QEC QEC.Coding QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale) (sigma : Word3 S)
    (hq : ∀ q, restrictWordLinear ((LQ S).syndromeRegion q)
      (rxSigmaAfterCx (A S) sigma) = 0) :
    d3 S (cqCorrectionTotal (A S) sigma) = 0 := by
  classical
  change d3 S (∑ q, cqComponentTotal (A S) sigma q) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero (fun q _ => actual_cq_boundary_zero S sigma hq q)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
