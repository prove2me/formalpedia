-- Prove2me | solution 1 for ThreeSum.LightLocalCoverInitResources.envelope_le_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:32:34.452781+00:00
-- url     : https://prove2.me/submissions/ebd6bdbd-ed2a-48db-b6bd-229ddaaf9f84

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_Scales_muZero_eq_twice_half


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverInitResources
theorem _root_.solution {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    envelope (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 5000000 n := by
  unfold envelope Scales.localSearch
  rw [Scales.muZero_eq_twice_half]
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega
end ThreeSum.LightLocalCoverInitResources
