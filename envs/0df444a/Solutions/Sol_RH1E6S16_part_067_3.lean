-- Prove2me | solution 1 for RH1E6S16.part_067_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:09:16.151438+00:00
-- url     : https://prove2.me/submissions/7abf6c0d-aae3-4e00-88a7-4b8aba9290de

import Definitions.Def_RH1E6S16_D067_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0542 : RS5.BandZeros ((61365814595 : ℝ) / 65536) ((61370206619 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0542.s0 RH1E6S16_0542.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0542.s0 RH1E6S16_0542.rest = RH1E6S16_0542.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0542.s0 :: RH1E6S16_0542.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0542.s0.t = ((61365814595 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0542.s0]
  have e1 : RH1E6S16_0542.sL.t = ((61370206619 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0542.sL]
  rw [e0, e1] at h
  exact h

theorem band_0543 : RS5.BandZeros ((61370206619 : ℝ) / 65536) ((61374571926 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0543.s0 RH1E6S16_0543.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0543.s0 RH1E6S16_0543.rest = RH1E6S16_0543.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0543.s0 :: RH1E6S16_0543.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0543.s0.t = ((61370206619 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0543.s0]
  have e1 : RH1E6S16_0543.sL.t = ((61374571926 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0543.sL]
  rw [e0, e1] at h
  exact h

theorem part_067_3 : RS5.BandZeros ((61365814595 : ℝ) / 65536) ((61374571926 : ℝ) / 65536) 254 := by
  have g0 := band_0542
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0543
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61365814595 : ℝ) / 65536) ((61374571926 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_067_3 <;> assumption
