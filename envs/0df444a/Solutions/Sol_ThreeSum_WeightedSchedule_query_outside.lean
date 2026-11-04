-- Prove2me | solution 1 for ThreeSum.WeightedSchedule.query_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:11.680442+00:00
-- url     : https://prove2.me/submissions/b9a91ee8-977c-4296-944f-52a7413973a7

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
import Theorems.Thm_ThreeSum_WeightedSchedule_output_cost

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration
namespace ThreeSum.WeightedSchedule
theorem _root_.solution {m : ℕ} {Q : TritWord (fixedLength m)}
    (hm : 0<m) (hQ : HasType Q (fixedPi m)) : bankCut m<cacheCost Q := by
  rw [output_cost hQ]; unfold dropBudget; omega
end ThreeSum.WeightedSchedule
