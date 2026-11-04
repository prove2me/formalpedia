-- Prove2me | solution 1 for ThreeSum.TernaryMomentSchedule.aggregate_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:45:21.090105+00:00
-- url     : https://prove2.me/submissions/3a280ced-439a-49f2-870b-c2bb8667b2c3

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentSchedule
open Finset TernaryJointType
open scoped BigOperators
namespace ThreeSum.TernaryMomentSchedule
theorem _root_.solution (score : ℕ→ℕ→ℕ→ℤ) (k i : ℕ) :
    aggregate [] score k i=0 := rfl
end ThreeSum.TernaryMomentSchedule
