-- Prove2me | solution 1 for ThreeSum.LightBandRawAResources.depth_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:44:09.314057+00:00
-- url     : https://prove2.me/submissions/2bbee806-c3e7-45c3-8668-5e2560a3666e

import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Theorems.Thm_ThreeSum_LightBandRawAResources_factor_bounds
import Theorems.Thm_ThreeSum_ColorBandBounds_depth_le
import Theorems.Thm_ThreeSum_LightBandRawAResources_depth_le
import Theorems.Thm_ThreeSum_LightScales_inputBits_le_self


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light Scales BandScales StageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace ThreeSum.LightBandRawAResources
theorem _root_.solution (n : ℕ) : LightBandRawAColor.depth (inputBits n+1) n (bandSize n) ≤ envelope n := by
  obtain ⟨h1,hn,_,_,_⟩ := factor_bounds n
  have hW : inputBits n+1 ≤ base n := (Nat.add_le_add_right (LightScales.inputBits_le_self n) 1).trans hn
  have hh := depth_le (inputBits n+1) n (bandSize n)
  unfold envelope
  omega
end ThreeSum.LightBandRawAResources
