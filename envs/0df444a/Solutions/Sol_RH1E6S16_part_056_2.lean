-- Prove2me | solution 1 for RH1E6S16.part_056_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T17:28:21.464535+00:00
-- url     : https://prove2.me/submissions/bed33667-d74c-4ea8-bc02-8dac0a672cb9

import Definitions.Def_RH1E6S16_D056_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0452 : RS5.BandZeros ((60970576498 : ℝ) / 65536) ((60974979305 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0452.s0 RH1E6S16_0452.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0452.s0 RH1E6S16_0452.rest = RH1E6S16_0452.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0452.s0 :: RH1E6S16_0452.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0452.s0.t = ((60970576498 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0452.s0]
  have e1 : RH1E6S16_0452.sL.t = ((60974979305 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0452.sL]
  rw [e0, e1] at h
  exact h

theorem band_0453 : RS5.BandZeros ((60974979305 : ℝ) / 65536) ((60979378666 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0453.s0 RH1E6S16_0453.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0453.s0 RH1E6S16_0453.rest = RH1E6S16_0453.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0453.s0 :: RH1E6S16_0453.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0453.s0.t = ((60974979305 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0453.s0]
  have e1 : RH1E6S16_0453.sL.t = ((60979378666 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0453.sL]
  rw [e0, e1] at h
  exact h

theorem part_056_2 : RS5.BandZeros ((60970576498 : ℝ) / 65536) ((60979378666 : ℝ) / 65536) 254 := by
  have g0 := band_0452
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0453
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60970576498 : ℝ) / 65536) ((60979378666 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_056_2 <;> assumption
