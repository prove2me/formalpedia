-- Prove2me | solution 1 for ThreeSum.WeightedGlobalBank.rank_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:17.435886+00:00
-- url     : https://prove2.me/submissions/fef3f3fe-5d56-4d1e-be1b-86525ae03a5e

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBank_rank_mono


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalBank
open TernaryJointType
namespace ThreeSum.WeightedGlobalBank
theorem _root_.solution {N : ℕ} {R Q : TritWord N} (h : Below R Q) : rank R≤rank Q := TernaryBank.rank_mono h
end ThreeSum.WeightedGlobalBank
