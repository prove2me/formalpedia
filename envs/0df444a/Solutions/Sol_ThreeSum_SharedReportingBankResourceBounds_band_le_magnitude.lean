-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.band_le_magnitude
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:52:01.868674+00:00
-- url     : https://prove2.me/submissions/b4a4c187-b7b4-469e-bc5d-3a4b202d1ad0

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
import Definitions.Def_WeightedCache3SUM_Alias_32619216de5760ac
import Theorems.Thm_ThreeSum_BlockSourceSharing_width_eq
import Theorems.Thm_ThreeSum_SourceBandCosts_bandSize_le_fullOutputs


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution (n : ℕ) : BandScales.bandSize n ≤ magnitude n := by
  have hB := SourceBandCosts.bandSize_le_fullOutputs n
  have hfull : TrimScales.fullOutputs n ≤ 2^(width (half n) (blocks n)) := by
    rw [show width (half n) (blocks n)=256*mu n from BlockSourceSharing.width_eq n]
    exact Nat.choose_le_two_pow _ _
  exact (hB.trans hfull).trans ((Nat.pow_le_pow_right (by decide) (by omega : width (half n) (blocks n) ≤
    width (half n) (blocks n)+1)).trans (components n).widthPower)
end ThreeSum.SharedReportingBankResourceBounds
