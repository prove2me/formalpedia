-- Prove2me | solution 1 for ThreeSum.BandPartition.size_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:03:30.018854+00:00
-- url     : https://prove2.me/submissions/4f530bc7-ab1e-4d24-895e-18e1f0e0f6a1

import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_BandPartition

set_option autoImplicit false
open ThreeSum ThreeSum.BandPartition
namespace ThreeSum.BandPartition
theorem _root_.solution {n m g : ℕ} (h : n ≤ m) : size n g ≤ size m g := by
  by_cases hn : n = 0
  · simp [size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [size,if_neg hn,if_neg hm]
    omega
end ThreeSum.BandPartition
