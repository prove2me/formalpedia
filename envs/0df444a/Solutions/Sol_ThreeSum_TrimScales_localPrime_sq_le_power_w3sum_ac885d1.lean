-- Prove2me | solution 1 for ThreeSum.TrimScales.localPrime_sq_le_power_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:26.625624+00:00
-- url     : https://prove2.me/submissions/8076c9b8-abf1-44f9-893b-0b890cffa684

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_sq_upper


set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution (h : ℕ) :
    LocalCoverBounds.localPrime h ^ 2 ≤ 2 ^ (4 + 514 * h) := by
  have hM : LocalCoverBounds.outputCount (512 * h) h ≤ 2 ^ (512 * h) :=
    Nat.choose_le_two_pow _ _
  calc
    LocalCoverBounds.localPrime h ^ 2 ≤
        16 * (LocalCoverBounds.outputCount (512 * h) h * 2 ^ (2 * h)) :=
      LocalCoverBounds.localPrime_sq_upper h
    _ ≤ 16 * (2 ^ (512 * h) * 2 ^ (2 * h)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hM)
    _ = 2 ^ (4 + 514 * h) := by
      rw [← pow_add, show 512 * h + 2 * h = 514 * h by omega, pow_add]
      norm_num
end ThreeSum.TrimScales
