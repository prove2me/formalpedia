-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.lower3_after_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:40:41.8182+00:00
-- url     : https://prove2.me/submissions/691248a2-3117-45fb-be0f-623f046f927f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_cx_total_boundary_zero
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_X_query_zero

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
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale) :
    rxSigmaAfterCx (A S) (lower3 S).val = (lower3 S).val := by
  have h := actual_cx_total_boundary_zero S (lower3 S).val (lower3_X_query_zero S)
  change (lower3 S).val + d3 S (cxCorrectionTotal (A S) (lower3 S).val) = (lower3 S).val
  rw [h,add_zero]
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
