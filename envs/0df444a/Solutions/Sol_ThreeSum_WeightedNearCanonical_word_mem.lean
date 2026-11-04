-- Prove2me | solution 1 for ThreeSum.WeightedNearCanonical.word_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:47.898217+00:00
-- url     : https://prove2.me/submissions/fda16aac-60b9-40c5-b290-7594acadf76d

import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_NearCanonical
import Theorems.Thm_ThreeSum_WeightedNearCanonical_wordList_word
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_wordList_admitted
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_words
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_words
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_wordList_admitted
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_words


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedNearCanonical
theorem _root_.solution {N D j : ℕ} (Q : TritWord N)
    (hj : j<(WeightedNearEnumeration.words (wordList Q) D).length) :
    word Q D j∈nearWords Q D := by
  apply (WeightedNearBankEnumeration.wordList_admitted Q _).mp
  rw [wordList_word Q hj]
  exact (WeightedNearEnumeration.mem_words _ _ _).mp (List.getElem_mem hj)
end ThreeSum.WeightedNearCanonical
