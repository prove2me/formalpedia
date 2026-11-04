-- Prove2me | solution 1 for ThreeSum.BandPartition.length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:02:24.680486+00:00
-- url     : https://prove2.me/submissions/1565aef3-f2d7-40e5-ac3e-e9cd4d54b0af

import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_BandPartition

set_option autoImplicit false
open ThreeSum ThreeSum.BandPartition
namespace ThreeSum.BandPartition
theorem _root_.solution (n g i : ℕ) : stop n g i-start g i ≤ g := by
  have hle : stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega
end ThreeSum.BandPartition
