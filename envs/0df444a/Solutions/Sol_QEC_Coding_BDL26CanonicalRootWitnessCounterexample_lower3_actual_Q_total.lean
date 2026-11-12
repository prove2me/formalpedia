-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.lower3_actual_Q_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:45:54.675412+00:00
-- url     : https://prove2.me/submissions/f6069990-6f51-4ea6-9153-44cb9414db26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_cq_reselect
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_Q_query
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_after_X

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
    cqCorrectionTotal (A S) (lower3 S).val = G S := by
  classical
  change (∑ q, cqComponentTotal (A S) (lower3 S).val q) = _
  apply Finset.sum_congr rfl
  intro q _
  exact actual_cq_reselect S (lower3 S).val q (localQuery S q) (localQuery_range S q)
    (by rw [lower3_after_X]; exact lower3_Q_query S q)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
