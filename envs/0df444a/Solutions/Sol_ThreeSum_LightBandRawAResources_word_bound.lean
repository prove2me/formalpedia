-- Prove2me | solution 1 for ThreeSum.LightBandRawAResources.word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:10:24.49458+00:00
-- url     : https://prove2.me/submissions/17edd312-4b0f-4802-8994-6ae3a4d33684

import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Theorems.Thm_ThreeSum_LightBandRawAResources_factor_bounds
import Theorems.Thm_ThreeSum_LightBandRawAResources_color_power_le
import Theorems.Thm_ThreeSum_ColorBandBounds_word_le
import Theorems.Thm_ThreeSum_LightBandRawAResources_word_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_band_le_magnitude


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light Scales BandScales StageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace ThreeSum.LightBandRawAResources
theorem _root_.solution (n U : ℕ) :
    LightBandRawAColor.word (inputBits n+1) n (bandSize n) U ≤ envelope n*(U+1) := by
  obtain ⟨h1,hn,hn2,hm,_⟩ := factor_bounds n
  have hg := (SharedReportingBankResourceBounds.band_le_magnitude n).trans hm
  have hp := (color_power_le n).trans (Nat.mul_le_mul_left 4 hn)
  have hh := word_le (inputBits n+1) n (bandSize n) U
  have hsum : LightBandRawAColor.word (inputBits n+1) n (bandSize n) U ≤ 138*base n+9*U := by omega
  have hb : base n ≤ base n*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hU : U ≤ base n*(U+1) := (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ h1)
  rw [show envelope n*(U+1)=1000*(base n*(U+1)) by unfold envelope; ring]
  omega
end ThreeSum.LightBandRawAResources
