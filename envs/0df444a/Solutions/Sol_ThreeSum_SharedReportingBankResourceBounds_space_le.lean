-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.space_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:39:48.740195+00:00
-- url     : https://prove2.me/submissions/944b1b87-2d72-4162-9623-9cfd5eb22620

import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Definitions.Def_WeightedCache3SUM_Alias_50a65a6ff3168d70
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_total_le
import Theorems.Thm_ThreeSum_SharedReportingBankCosts_total_le
import Theorems.Thm_ThreeSum_SourceBuckets_offset_le


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows
set_option maxHeartbeats 2800000
set_option maxRecDepth 14000
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution {free h J NB NC g n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    LightSharedReportingHost.space free h J NB NC g ≤ free+extent h J n := by
  have hP := total_le (h := h) (J := J) (g := g) hB hC
  have ho := offset_le h J
  have hm := Nat.mul_le_mul_left (total h J NB NC g) ho
  have hp := Nat.mul_le_mul_right (5*levels J+levels J*cellBound h J) hP
  unfold LightSharedReportingHost.space
  apply max_le
  · unfold records LightPascal.tableSize extent
    omega
  · unfold SharedReportingBankHeader.finish rowBase payload records extent
    nlinarith
end ThreeSum.SharedReportingBankResourceBounds
