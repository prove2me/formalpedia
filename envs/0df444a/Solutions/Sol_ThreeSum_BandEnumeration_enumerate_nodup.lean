-- Prove2me | solution 1 for ThreeSum.BandEnumeration.enumerate_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:19.21935+00:00
-- url     : https://prove2.me/submissions/4cd2f940-7294-49c4-aa1c-32292e9b351a

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Theorems.Thm_ThreeSum_BandEnumeration_checkedCandidate_sound
import Theorems.Thm_ThreeSum_BandEnumeration_owners_nodup

set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family
namespace ThreeSum.BandEnumeration
theorem _root_.solution (A B C : Family) : (enumerate A B C).Nodup := by
  apply List.Nodup.filterMap _ (owners_nodup A B C)
  intro o o' t ho ho'
  have h := checkedCandidate_sound A B C o (by simpa only [Option.mem_def] using ho)
  have h' := checkedCandidate_sound A B C o' (by simpa only [Option.mem_def] using ho')
  exact h.2.symm.trans h'.2
end ThreeSum.BandEnumeration
