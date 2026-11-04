-- Prove2me | solution 1 for ThreeSum.TernaryNearCanonical.word_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:16:22.562403+00:00
-- url     : https://prove2.me/submissions/89d354aa-54c0-4163-877a-a59f70e94b77

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
import Theorems.Thm_ThreeSum_TernaryNearCanonical_wordList_word
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_wordList_admitted
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_words


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryNearCanonical
theorem _root_.solution {N D j : ℕ} (Q : TritWord N)
    (hj : j<(TernaryNearEnumeration.words (wordList Q) D).length) :
    word Q D j∈nearWords Q D := by
  apply (TernaryNearBankEnumeration.wordList_admitted Q _).mp
  rw [wordList_word Q hj]
  exact (TernaryNearEnumeration.mem_words _ _ _).mp (List.getElem_mem hj)
end ThreeSum.TernaryNearCanonical
