-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.scale_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:53:46.249436+00:00
-- url     : https://prove2.me/submissions/9f57cb78-7141-413e-a8c1-c5ddf978fc4d

import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Theorems.Thm_ThreeSum_EncodedColorResources_localEnvelope_powerBound
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_identity_powerBound
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_maxMod_powerBound
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_window_powerBound
import Theorems.Thm_ThreeSum_Parameters_E_bounds
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_magnitude_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mono_exponent


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter
set_option maxHeartbeats 2200000
set_option maxRecDepth 13000
noncomputable section
namespace ThreeSum.EncodedColorResources
theorem _root_.solution : PowerBound scale 2048 := by
  have hl := localEnvelope_powerBound.mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  have hp := maxMod_powerBound.mono_exponent (show (Parameters.E+1/2)/5 ≤ (2048 : ℝ) by
    have hh := Parameters.E_bounds.2; linarith)
  have hy := window_powerBound.mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  have hn := identity_powerBound.mono_exponent (by norm_num : (1 : ℝ) ≤ 2048)
  have hc := (PowerBound.const 100).mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  exact ((((SharedReportingBankResourceBounds.magnitude_powerBound.add_same hl).add_same hp).add_same hy).add_same hn).add_same hc
end ThreeSum.EncodedColorResources
