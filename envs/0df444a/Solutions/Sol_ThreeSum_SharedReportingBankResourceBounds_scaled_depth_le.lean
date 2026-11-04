-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.scaled_depth_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:52:09.613245+00:00
-- url     : https://prove2.me/submissions/18a39bef-f811-4ea3-ab2b-1d60f9d3aefa

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
import Definitions.Def_WeightedCache3SUM_Alias_32619216de5760ac

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution (n : ℕ) : scaledDepth n ≤ polynomialPart n := by
  have H := components n
  have hM := H.positive
  have hL := H.localWidthBound
  have hW := H.widthBound
  have hK := H.levelsBound
  have hp : magnitude n+1 ≤ (magnitude n+1)^5 := Nat.le_self_pow (by decide) _
  have hn : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hm := Nat.le_mul_of_pos_right (5000*(magnitude n+1)^5) hn
  unfold scaledDepth depth polynomialPart
  nlinarith
end ThreeSum.SharedReportingBankResourceBounds
