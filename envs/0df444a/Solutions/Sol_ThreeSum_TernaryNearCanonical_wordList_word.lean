-- Prove2me | solution 1 for ThreeSum.TernaryNearCanonical.wordList_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:11:04.7482+00:00
-- url     : https://prove2.me/submissions/6865657c-6142-496b-97cf-070220b0f004

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_fromList


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryNearCanonical
theorem _root_.solution {N D j : ℕ} (Q : TritWord N)
    (hj : j<(TernaryNearEnumeration.words (wordList Q) D).length) :
    wordList (word Q D j)=(TernaryNearEnumeration.words (wordList Q) D)[j] := by
  unfold word
  rw [dif_pos hj]
  exact wordList_fromList _ _ _
end ThreeSum.TernaryNearCanonical
