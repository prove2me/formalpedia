-- Prove2me | solution 1 for ThreeSum.BandScales.bandSize_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:49.257265+00:00
-- url     : https://prove2.me/submissions/5a4d4d9f-c546-46ab-a297-5bc8d110ff6e

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
import Theorems.Thm_ThreeSum_BandScales_bandRoot_pos
import Theorems.Thm_ThreeSum_BandScales_bandSize_mul_bounds

set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
namespace ThreeSum.BandScales
theorem _root_.solution (n : ℕ) : 0 < bandSize n := by
  have hl := (bandSize_mul_bounds n).1
  have hp := bandRoot_pos n
  by_contra h
  have hb : bandSize n = 0 := by omega
  rw [hb, Nat.mul_zero] at hl
  omega
end ThreeSum.BandScales
