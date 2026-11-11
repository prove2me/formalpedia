-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.actualInputs_readout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:08:48.953207+00:00
-- url     : https://prove2.me/submissions/eb9cb22d-08c2-49eb-a6d5-daa63aeef5c8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixHistory_top_eq
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixInput_readout
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_syndromeReadout_physical
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
universe u
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (sigma : TopInput S n) (a : LevelIndex n) :
    actualReadout S n sigma a = (actualInputs S n sigma a).val := by
  let st := LevelTwoHistory.suffixSteps (indexedDecoderData S (n+2)) (actualAboveTwoSteps S n)
  let s : (SuffixData S n).family.Syndrome (TopIndex n) := sigma
  have he := prefixHistory_top_eq (SuffixData S n) st (actualBase S n) s
  have hr := prefixInput_readout (SuffixData S n) st (actualBase S n) n
    (Nat.le_refl _) s a (Nat.le_of_lt_succ a.isLt)
  have hp := LevelTwoHistory.syndromeReadout_physical (indexedDecoderData S (n+2))
    (actualHistory S n sigma) a
  exact hp.trans ((congrArg (fun H : CorrectionHistory (SuffixData S n) =>
    historyInputReadout (SuffixData S n) H a) he).symm.trans hr)
end QEC.Coding.BDL26HistorySyndromeSensitivity
