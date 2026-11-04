-- Prove2me | solution 1 for ThreeSum.WeightedFrozenQueryCost.wordList_capWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:06.900071+00:00
-- url     : https://prove2.me/submissions/d97d8d16-141a-4afa-8297-85300dd3dd8e

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_wordList_capWord


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration
namespace ThreeSum.WeightedFrozenQueryCost
theorem _root_.solution {N : ℕ} (coords : List (Fin N)) (R : Word N) :
    WeightedBankEnumeration.wordList (capWord coords R)=caps coords R :=
  TernaryFrozenQueryCost.wordList_capWord coords R
end ThreeSum.WeightedFrozenQueryCost
