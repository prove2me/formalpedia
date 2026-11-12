-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.localZWitnessLower_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:27:41.70245+00:00
-- url     : https://prove2.me/submissions/be79cb0d-9473-4b54-bf35-1f5df5f2381c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (S : OddScale) : (localZWitnessLower S).val =
    BDL26UniformHistoryObstruction.lowerSyndromeRaw S 0 := by
  change (indexedFamily S 2).coboundary1 1 _ = _
  rw [indexedFamily_coboundary1]
  rfl
end QEC.Coding.BDL26CanonicalHistoryMarks
