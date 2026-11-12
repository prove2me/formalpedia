-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_nonzero_Q_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:50:02.58149+00:00
-- url     : https://prove2.me/submissions/158e9f13-1891-4a25-828e-98a76369fc68

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_Q_query
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_rootMask_localQ_query_nonzero

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
    ∃ p : LocalRegionIndex ((LQ S).syndromeRegion (q2 S)),
      (lower3 S).val p.val ≠ 0 := by
  by_contra h
  push_neg at h
  apply rootMask_localQ_query_nonzero S
  rw [← lower3_Q_query S (q2 S)]
  funext p
  exact h p
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
