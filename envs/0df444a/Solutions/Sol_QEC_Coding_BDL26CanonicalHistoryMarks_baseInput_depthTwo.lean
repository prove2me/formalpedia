-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.baseInput_depthTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:51:27.478909+00:00
-- url     : https://prove2.me/submissions/f348c961-9fc1-41c4-92eb-2fd7882ac395

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_inputAt_base
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_buildCorrectionHistory_zero
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
variable (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (s : Input S 0) : baseInput S 0 s = s := by
  have hh := buildCorrectionHistory_zero (Data S 0)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S 0)) (actualBase S 0) s
  let B : RecursiveBaseLevelCorrection (Data S 0) :=
    { input := s, correction := (actualBase S 0).decode s,
      relation := ((actualBase S 0).rightInverse s).symm }
  have hm : CorrectionHistoryEntry.base B ∈ actualHistory S 0 s := by
    rw [show actualHistory S 0 s = [.base B] from hh]
    exact List.mem_singleton_self _
  exact inputAt_base S 0 s B hm
end QEC.Coding.BDL26CanonicalHistoryMarks
