-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_localQ_query_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:45:09.437902+00:00
-- url     : https://prove2.me/submissions/e06c4637-1ce5-4e22-b2b3-b80db5d3b9b1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_terminalSyndrome_ne_zero
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_localSeed_at_q2

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
theorem _root_.solution (S : OddScale) :
    localQuery S (q2 S) ≠ 0 := by
  rw [localQuery,localSeed_at_q2]
  exact terminalSyndrome_ne_zero S (q2 S) (r2 S) (q2_incidence S)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
