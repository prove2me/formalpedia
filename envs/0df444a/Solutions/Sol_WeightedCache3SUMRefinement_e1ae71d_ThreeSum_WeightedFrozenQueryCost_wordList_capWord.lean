-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost.wordList_capWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:09:40.689502+00:00
-- url     : https://prove2.me/submissions/19160ef9-e9e6-4d00-bc3c-d97f931f716b

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_wordList_capWord


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost
theorem _root_.solution {N : ℕ} (coords : List (Fin N)) (R : Word N) :
    WeightedBankEnumeration.wordList (capWord coords R)=caps coords R :=
  TernaryFrozenQueryCost.wordList_capWord coords R
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost
