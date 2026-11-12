-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.localW_at_q2_imbalance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:37:36.427723+00:00
-- url     : https://prove2.me/submissions/47d3dabc-98cb-41b8-ac58-382346ff96ee

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actualQSection_spec
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_terminal_solution_imbalance
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_localSeed_at_q2
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) 0) +
      localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) 1) = 1 := by
  apply terminal_solution_imbalance
  exact (actualQSection_spec S (q2 S) (localQuery S (q2 S))
    (localQuery_range S (q2 S))).1.trans (by
      rw [localQuery, localSeed_at_q2]
      rfl)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
