-- Prove2me | solution 1 for RH1E6S14.part_080_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:07:51.854557+00:00
-- url     : https://prove2.me/submissions/76d547e8-1110-4bbb-917e-4e44837a9eed

import Definitions.Def_RH1E6S14_D080_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0644 : RS5.BandZeros ((55287431526 : ℝ) / 65536) ((55291860908 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0644.s0 RH1E6S14_0644.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0644.s0 RH1E6S14_0644.rest = RH1E6S14_0644.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0644.s0 :: RH1E6S14_0644.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0644.s0.t = ((55287431526 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0644.s0]
  have e1 : RH1E6S14_0644.sL.t = ((55291860908 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0644.sL]
  rw [e0, e1] at h
  exact h

theorem band_0645 : RS5.BandZeros ((55291860908 : ℝ) / 65536) ((55296286394 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0645.s0 RH1E6S14_0645.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0645.s0 RH1E6S14_0645.rest = RH1E6S14_0645.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0645.s0 :: RH1E6S14_0645.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0645.s0.t = ((55291860908 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0645.s0]
  have e1 : RH1E6S14_0645.sL.t = ((55296286394 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0645.sL]
  rw [e0, e1] at h
  exact h

theorem part_080_2 : RS5.BandZeros ((55287431526 : ℝ) / 65536) ((55296286394 : ℝ) / 65536) 254 := by
  have g0 := band_0644
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0645
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55287431526 : ℝ) / 65536) ((55296286394 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_080_2 <;> assumption
