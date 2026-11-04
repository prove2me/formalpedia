-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.incidence_cap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:28:49.105189+00:00
-- url     : https://prove2.me/submissions/d87111fe-7d05-4c4f-8b11-46af9e5243d3

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Theorems.Thm_ThreeSum_EncodedColorResources_count_le
import Theorems.Thm_ThreeSum_ColorBandBounds_count_le
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_count_le
import Definitions.Def_WeightedCache3SUM_Alias_aa1db49eeb0333a7
import Theorems.Thm_ThreeSum_LightBandRawAResources_count_le
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_le
import Theorems.Thm_ThreeSum_ModuloCounts_count_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_count_le


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n : ℕ) : EncodedColorStageCosts.incidenceCap n ≤ 3*(scale n)^3 := by
  have hh := Nat.mul_le_mul (dimensions n).2.2.2.1 (count_le n)
  unfold EncodedColorStageCosts.incidenceCap
  nlinarith only [hh]
end ThreeSum.EncodedColorResources
