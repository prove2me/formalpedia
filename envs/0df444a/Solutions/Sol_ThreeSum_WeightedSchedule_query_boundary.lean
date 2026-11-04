-- Prove2me | solution 1 for ThreeSum.WeightedSchedule.query_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:13.205488+00:00
-- url     : https://prove2.me/submissions/a21b36f4-da01-437c-80fa-4d960c9b6b75

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
    (hQ : HasType Q (fixedPi m)) : cacheCost Q+1024-bankCut m=treeBudget m := by
  rw [output_cost hQ]; unfold treeBudget; omega
end ThreeSum.WeightedSchedule
