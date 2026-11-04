-- Prove2me | solution 1 for ThreeSum.LightBandRawAResources.base_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:03:09.635387+00:00
-- url     : https://prove2.me/submissions/b2858f71-8d50-4316-a23e-2a67fcdc5bdb

import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_identity_powerBound
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_magnitude_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mono_exponent
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_pow


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light Scales BandScales StageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
noncomputable section
namespace ThreeSum.LightBandRawAResources
theorem _root_.solution : PowerBound base 2050 := by
  have hm := SharedReportingBankResourceBounds.magnitude_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 2048))
  have hn := ArithmeticStageBounds.identity_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have hh := hm.mul (hn.pow 2)
  convert hh using 1 <;> (first | rfl | norm_num [base])
end ThreeSum.LightBandRawAResources
