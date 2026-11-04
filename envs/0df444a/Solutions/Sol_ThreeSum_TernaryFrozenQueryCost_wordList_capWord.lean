-- Prove2me | solution 1 for ThreeSum.TernaryFrozenQueryCost.wordList_capWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:12:50.783233+00:00
-- url     : https://prove2.me/submissions/002227af-426f-4c8c-982f-42bcd42f4ba8

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_fromList


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryCost
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryFrozenQueryCost
theorem _root_.solution {N : ℕ} (coords : List (Fin N)) (R : TritWord N) :
    TernaryBankEnumeration.wordList (capWord coords R)=caps coords R :=
  TernaryBankEnumeration.wordList_fromList _ _ _
end ThreeSum.TernaryFrozenQueryCost
