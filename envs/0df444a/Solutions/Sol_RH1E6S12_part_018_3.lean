-- Prove2me | solution 1 for RH1E6S12.part_018_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T08:20:05.4838+00:00
-- url     : https://prove2.me/submissions/479cb617-8f78-4595-b0a4-0120f809eefe

import Definitions.Def_RH1E6S12_D018_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0150 : RS5.BandZeros ((46549808228 : ℝ) / 65536) ((46554298088 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0150.s0 RH1E6S12_0150.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0150.s0 RH1E6S12_0150.rest = RH1E6S12_0150.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0150.s0 :: RH1E6S12_0150.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0150.s0.t = ((46549808228 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0150.s0]
  have e1 : RH1E6S12_0150.sL.t = ((46554298088 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0150.sL]
  rw [e0, e1] at h
  exact h

theorem band_0151 : RS5.BandZeros ((46554298088 : ℝ) / 65536) ((46558804274 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0151.s0 RH1E6S12_0151.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0151.s0 RH1E6S12_0151.rest = RH1E6S12_0151.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0151.s0 :: RH1E6S12_0151.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0151.s0.t = ((46554298088 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0151.s0]
  have e1 : RH1E6S12_0151.sL.t = ((46558804274 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0151.sL]
  rw [e0, e1] at h
  exact h

theorem part_018_3 : RS5.BandZeros ((46549808228 : ℝ) / 65536) ((46558804274 : ℝ) / 65536) 254 := by
  have g0 := band_0150
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0151
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46549808228 : ℝ) / 65536) ((46558804274 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_018_3 <;> assumption
