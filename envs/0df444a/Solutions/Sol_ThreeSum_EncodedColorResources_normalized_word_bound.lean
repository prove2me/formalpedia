-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.normalized_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:42:52.963209+00:00
-- url     : https://prove2.me/submissions/4bb18e59-0844-4ec8-8e99-16e08dffbf8c

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Theorems.Thm_ThreeSum_EncodedColorResources_count_le
import Theorems.Thm_ThreeSum_ColorBandBounds_count_le
import Theorems.Thm_ThreeSum_ColorBandBounds_word_le
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_count_le
import Definitions.Def_WeightedCache3SUM_Alias_aa1db49eeb0333a7
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Theorems.Thm_ThreeSum_EncodedColorStageCosts_word_le
import Theorems.Thm_ThreeSum_LightBandRawAResources_color_power_le
import Theorems.Thm_ThreeSum_LightBandRawAResources_count_le
import Theorems.Thm_ThreeSum_LightBandRawAResources_word_le
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_LightScales_inputBits_le_self
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_le
import Theorems.Thm_ThreeSum_ModuloCounts_count_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_count_le
import Theorems.Thm_ThreeSum_SourceFiniteCosts_word_le


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n U : ℕ) : LightEncodedColorNormalize.word n U ≤ 400*(scale n)^2+9*U := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hg := (dimensions n).2.2.2.1
  have hW := (Nat.add_le_add_right (LightScales.inputBits_le_self n) 1).trans hn
  have hpow := (LightBandRawAResources.color_power_le n).trans (Nat.mul_le_mul_left 4 hn)
  have hcount := count_le n
  have hn2 := Nat.pow_le_pow_left (show n ≤ scale n by omega) 2
  have hraw := LightBandRawAResources.word_le (inputBits n+1) n (bandSize n) U
  unfold LightEncodedColorNormalize.word LightEncodedColorLayout.word
  nlinarith only [hb,hn,hg,hW,hpow,hcount,hn2,hraw]
end ThreeSum.EncodedColorResources
