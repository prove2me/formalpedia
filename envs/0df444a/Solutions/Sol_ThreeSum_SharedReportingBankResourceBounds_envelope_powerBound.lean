-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.envelope_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:02:34.357674+00:00
-- url     : https://prove2.me/submissions/a3a9702c-93be-40d6-9de3-3ce910927fbd

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_magnitude_powerBound
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_polynomial_part_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mono_exponent
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_pow


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales StageBounds Filter Light
open scoped Topology
set_option maxHeartbeats 1200000
set_option maxRecDepth 14000
noncomputable section
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution : PowerBound envelope 131072 := by
  have hp := polynomial_part_powerBound.mono_exponent
    (by norm_num : (10242 : ℝ) ≤ 131072)
  have hm : PowerBound (fun n => (magnitude n)^64) 131072 := by
    convert magnitude_powerBound.pow 64 using 1 <;> norm_num
  exact hp.add_same hm
end ThreeSum.SharedReportingBankResourceBounds
