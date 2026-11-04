-- Prove2me | solution 1 for ThreeSum.BandPartition.index_lt_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:12:56.30212+00:00
-- url     : https://prove2.me/submissions/7d90bb04-d232-4bd5-a482-e5b46defb74f

import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_BandPartition

set_option autoImplicit false
open ThreeSum ThreeSum.BandPartition
namespace ThreeSum.BandPartition
theorem _root_.solution {n g i : ℕ} (hi : i < n) : i/g < size n g := by
  have hn : n ≠ 0 := by omega
  have hh := Nat.div_le_div_right (c := g) (show i ≤ n-1 by omega)
  simp only [size,if_neg hn]
  omega
end ThreeSum.BandPartition
