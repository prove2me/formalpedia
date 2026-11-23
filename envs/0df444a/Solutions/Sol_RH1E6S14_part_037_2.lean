-- Prove2me | solution 1 for RH1E6S14.part_037_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:43:46.511668+00:00
-- url     : https://prove2.me/submissions/ddd8105b-cbc2-4611-8d83-22d5c93ff0de

import Definitions.Def_RH1E6S14_D037_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0300 : RS5.BandZeros ((53762059461 : ℝ) / 65536) ((53766498934 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0300.s0 RH1E6S14_0300.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0300.s0 RH1E6S14_0300.rest = RH1E6S14_0300.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0300.s0 :: RH1E6S14_0300.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0300.s0.t = ((53762059461 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0300.s0]
  have e1 : RH1E6S14_0300.sL.t = ((53766498934 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0300.sL]
  rw [e0, e1] at h
  exact h

theorem band_0301 : RS5.BandZeros ((53766498934 : ℝ) / 65536) ((53770934818 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0301.s0 RH1E6S14_0301.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0301.s0 RH1E6S14_0301.rest = RH1E6S14_0301.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0301.s0 :: RH1E6S14_0301.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0301.s0.t = ((53766498934 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0301.s0]
  have e1 : RH1E6S14_0301.sL.t = ((53770934818 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0301.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_2 : RS5.BandZeros ((53762059461 : ℝ) / 65536) ((53770934818 : ℝ) / 65536) 254 := by
  have g0 := band_0300
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0301
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53762059461 : ℝ) / 65536) ((53770934818 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_037_2 <;> assumption
