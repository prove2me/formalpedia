-- Prove2me | solution 1 for ThreeSum.RawAKeyLists.key_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:42.49358+00:00
-- url     : https://prove2.me/submissions/13185ea4-4a1e-4744-9bcc-30d9280d9418

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_ThreeSum_RawIncidences_lift_small


set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000
namespace ThreeSum.RawAKeyLists
theorem _root_.solution {P : ℤ} (hP : 0 < P) (xs : List ℤ) (r : Record xs) :
    |key P xs r| ≤ 2*P := by
  have hn := Int.emod_nonneg (xs.getD r.2.val 0) hP.ne'
  have hu := Int.emod_lt_of_pos (xs.getD r.2.val 0) hP
  have hl : -1 ≤ lift r.1 ∧ lift r.1 ≤ 1 := by
    rcases lift_small r.1 with hh | hh | hh <;> rw [hh] <;> norm_num
  unfold key
  apply abs_le.mpr
  constructor <;> nlinarith
end ThreeSum.RawAKeyLists
