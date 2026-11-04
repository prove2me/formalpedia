-- Prove2me | solution 1 for ThreeSum.TrimScales.localLength_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:11.428358+00:00
-- url     : https://prove2.me/submissions/b2b3576a-43be-48f8-90ca-c99281251d6b

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_TrimScales_localPrime_log2_sq_le
import Theorems.Thm_ThreeSum_LocalHashMoments_localSchedule_length


set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution (h : ℕ) :
    localLength h ≤ 2 ^ 19 * (h + 1) ^ 2 := by
  have hlog := localPrime_log2_sq_le h
  have hb : localLength h ≤ 320 * (2 * h + 1) * (514 * h + 5) := by
    rw [localLength, LocalHashMoments.localSchedule_length]
    exact Nat.mul_le_mul_left _ (by omega)
  norm_num
  nlinarith [hb]
end ThreeSum.TrimScales
