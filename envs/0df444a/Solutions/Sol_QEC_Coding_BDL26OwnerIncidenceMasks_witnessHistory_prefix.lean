-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.witnessHistory_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:17:40.502458+00:00
-- url     : https://prove2.me/submissions/726114f1-a538-4bdc-a9d5-1d948976b3ce

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessHistory_exact

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution : ∃ tail,
    actualHistory scaleFive 2 witnessUpper =
      CorrectionHistoryEntry.step (1 : StepIndex 2)
        (LevelTwoHistory.suffixOutput (indexedDecoderData scaleFive 4) 1 witnessTopOutput) ::
      CorrectionHistoryEntry.step (0 : StepIndex 2)
        (LevelTwoHistory.suffixOutput (indexedDecoderData scaleFive 4) 0 witnessNextOutput) :: tail := by
  exact ⟨[CorrectionHistoryEntry.base witnessBaseEntry], witnessHistory_exact⟩
end QEC.Coding.BDL26OwnerIncidenceMasks
