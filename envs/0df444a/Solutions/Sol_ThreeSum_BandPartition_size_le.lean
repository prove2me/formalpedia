-- Prove2me | solution 1 for ThreeSum.BandPartition.size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:56:52.827697+00:00
-- url     : https://prove2.me/submissions/b9567f4a-0178-4499-bf93-265392ac5487

import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_BandPartition

set_option autoImplicit false
open ThreeSum ThreeSum.BandPartition
namespace ThreeSum.BandPartition
theorem _root_.solution (n g : ℕ) : size n g ≤ n := by
  unfold size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega
end ThreeSum.BandPartition
