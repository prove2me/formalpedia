-- Prove2me | solution 1 for RH1E6S09.part_030_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:34:37.773716+00:00
-- url     : https://prove2.me/submissions/0bc4efc7-adfa-484c-bdf9-a56b2f9bd981

import Definitions.Def_RH1E6S09_D030_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0242 : RS5.BandZeros ((37155399319 : ℝ) / 65536) ((37159969516 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0242.s0 RH1E6S09_0242.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0242.s0 RH1E6S09_0242.rest = RH1E6S09_0242.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0242.s0 :: RH1E6S09_0242.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0242.s0.t = ((37155399319 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0242.s0]
  have e1 : RH1E6S09_0242.sL.t = ((37159969516 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0242.sL]
  rw [e0, e1] at h
  exact h

theorem band_0243 : RS5.BandZeros ((37159969516 : ℝ) / 65536) ((37164552248 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0243.s0 RH1E6S09_0243.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0243.s0 RH1E6S09_0243.rest = RH1E6S09_0243.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0243.s0 :: RH1E6S09_0243.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0243.s0.t = ((37159969516 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0243.s0]
  have e1 : RH1E6S09_0243.sL.t = ((37164552248 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0243.sL]
  rw [e0, e1] at h
  exact h

theorem part_030_1 : RS5.BandZeros ((37155399319 : ℝ) / 65536) ((37164552248 : ℝ) / 65536) 254 := by
  have g0 := band_0242
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0243
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37155399319 : ℝ) / 65536) ((37164552248 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_030_1 <;> assumption
