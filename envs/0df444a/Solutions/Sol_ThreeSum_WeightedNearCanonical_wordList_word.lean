-- Prove2me | solution 1 for ThreeSum.WeightedNearCanonical.wordList_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:11:52.110795+00:00
-- url     : https://prove2.me/submissions/d3ad5c8f-10ca-4e52-9900-b74cc73faa0b

import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_NearCanonical
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_fromList
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_fromList


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedNearCanonical
theorem _root_.solution {N D j : ℕ} (Q : TritWord N)
    (hj : j<(WeightedNearEnumeration.words (wordList Q) D).length) :
    wordList (word Q D j)=(WeightedNearEnumeration.words (wordList Q) D)[j] := by
  unfold word
  rw [dif_pos hj]
  exact wordList_fromList _ _ _
end ThreeSum.WeightedNearCanonical
