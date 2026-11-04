-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.cell_le_magnitude
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:05:10.4562+00:00
-- url     : https://prove2.me/submissions/79e8619c-e533-4bc2-ab0c-aa5eb6d75c5f

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
import Definitions.Def_WeightedCache3SUM_Alias_32619216de5760ac
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_prefix_storage_le_magnitude

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution (n : ℕ) : cellBound (half n) (blocks n) ≤ 20*(magnitude n+1)^3 := by
  have H := components n
  have hM := H.positive
  have hL := H.localWidthBound
  have hW := H.widthBound
  have hN := H.prefixBound
  have hE := H.pairsPower
  have hS := prefix_storage_le_magnitude n
  have hlocal : 2^(512*half n) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.localPower
  have hpower : 2^(width (half n) (blocks n)) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.widthPower
  have hquad := Nat.pow_le_pow_left hW 2
  have hbox := Nat.mul_le_mul (Nat.mul_le_mul hN hW) hpower
  unfold cellBound
  nlinarith
end ThreeSum.SharedReportingBankResourceBounds
