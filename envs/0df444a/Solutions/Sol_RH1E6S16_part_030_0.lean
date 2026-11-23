-- Prove2me | solution 1 for RH1E6S16.part_030_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:47:58.093676+00:00
-- url     : https://prove2.me/submissions/164cf71d-8b29-447c-97ed-3b36ff104622

import Definitions.Def_RH1E6S16_D030_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0240 : RS5.BandZeros ((60038767874 : ℝ) / 65536) ((60043150226 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0240.s0 RH1E6S16_0240.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0240.s0 RH1E6S16_0240.rest = RH1E6S16_0240.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0240.s0 :: RH1E6S16_0240.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0240.s0.t = ((60038767874 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0240.s0]
  have e1 : RH1E6S16_0240.sL.t = ((60043150226 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0240.sL]
  rw [e0, e1] at h
  exact h

theorem band_0241 : RS5.BandZeros ((60043150226 : ℝ) / 65536) ((60047559974 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0241.s0 RH1E6S16_0241.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0241.s0 RH1E6S16_0241.rest = RH1E6S16_0241.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0241.s0 :: RH1E6S16_0241.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0241.s0.t = ((60043150226 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0241.s0]
  have e1 : RH1E6S16_0241.sL.t = ((60047559974 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0241.sL]
  rw [e0, e1] at h
  exact h

theorem part_030_0 : RS5.BandZeros ((60038767874 : ℝ) / 65536) ((60047559974 : ℝ) / 65536) 254 := by
  have g0 := band_0240
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0241
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60038767874 : ℝ) / 65536) ((60047559974 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_030_0 <;> assumption
