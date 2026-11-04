-- Prove2me | solution 1 for ThreeSum.TernaryMomentSchedule.aggregate_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:46:04.613076+00:00
-- url     : https://prove2.me/submissions/959e83cd-2fe1-4463-958f-45de07211cb1

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentSchedule
open Finset TernaryJointType
open scoped BigOperators
namespace ThreeSum.TernaryMomentSchedule
theorem _root_.solution (c : ℕ×ℕ) (xs : List (ℕ×ℕ))
    (score : ℕ→ℕ→ℕ→ℤ) (k i : ℕ) :
    aggregate (c::xs) score k i=
      (if c.1=k then score c.1 c.2 i else 0)+aggregate xs score k i := rfl
end ThreeSum.TernaryMomentSchedule
