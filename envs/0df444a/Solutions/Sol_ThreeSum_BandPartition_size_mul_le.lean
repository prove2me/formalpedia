-- Prove2me | solution 1 for ThreeSum.BandPartition.size_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:25.036366+00:00
-- url     : https://prove2.me/submissions/10775548-c0d5-4c0b-80aa-b4be4ddbb9a8

import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_BandPartition

set_option autoImplicit false
open ThreeSum ThreeSum.BandPartition
namespace ThreeSum.BandPartition
theorem _root_.solution (n g : ℕ) : size n g*g ≤ n+g := by
  by_cases hn : n = 0
  · simp [size,hn]
  · have hd := Nat.div_mul_le_self (n-1) g
    simp only [size,if_neg hn,Nat.add_mul,Nat.one_mul]
    omega
end ThreeSum.BandPartition
