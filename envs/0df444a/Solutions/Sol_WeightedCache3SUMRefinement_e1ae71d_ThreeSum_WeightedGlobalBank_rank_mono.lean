-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.rank_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:10:28.673822+00:00
-- url     : https://prove2.me/submissions/a5f9d69d-1a20-4359-a058-603e232a486d

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBank_rank_mono


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
open TernaryJointType
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
theorem _root_.solution {N : ℕ} {R Q : TritWord N} (h : Below R Q) : rank R≤rank Q := TernaryBank.rank_mono h
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
