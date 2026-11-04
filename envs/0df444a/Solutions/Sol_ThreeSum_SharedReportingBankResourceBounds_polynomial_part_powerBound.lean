-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.polynomial_part_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:52:22.71642+00:00
-- url     : https://prove2.me/submissions/c67cfdde-5a73-4540-95b7-a8795c0f0533

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_magnitude_powerBound
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_identity_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mono_exponent
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_pow


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales StageBounds Filter Light
open scoped Topology
set_option maxHeartbeats 1200000
set_option maxRecDepth 14000
noncomputable section
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution : PowerBound polynomialPart 10242 := by
  have hm := magnitude_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 2048))
  have hn := ArithmeticStageBounds.identity_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have hh := ((PowerBound.const 5000).mul (hm.pow 5)).mul (hn.pow 2)
  convert hh using 1 <;> (first | rfl | norm_num [polynomialPart])
end ThreeSum.SharedReportingBankResourceBounds
