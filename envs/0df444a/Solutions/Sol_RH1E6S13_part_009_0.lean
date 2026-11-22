-- Prove2me | solution 1 for RH1E6S13.part_009_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T19:19:07.236449+00:00
-- url     : https://prove2.me/submissions/692538aa-e48e-4555-b7ae-52cc9f2c890d

import Definitions.Def_RH1E6S13_D009_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0072 : RS5.BandZeros ((49474019174 : ℝ) / 65536) ((49478472591 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0072.s0 RH1E6S13_0072.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0072.s0 RH1E6S13_0072.rest = RH1E6S13_0072.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0072.s0 :: RH1E6S13_0072.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0072.s0.t = ((49474019174 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0072.s0]
  have e1 : RH1E6S13_0072.sL.t = ((49478472591 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0072.sL]
  rw [e0, e1] at h
  exact h

theorem band_0073 : RS5.BandZeros ((49478472591 : ℝ) / 65536) ((49482952378 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0073.s0 RH1E6S13_0073.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0073.s0 RH1E6S13_0073.rest = RH1E6S13_0073.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0073.s0 :: RH1E6S13_0073.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0073.s0.t = ((49478472591 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0073.s0]
  have e1 : RH1E6S13_0073.sL.t = ((49482952378 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0073.sL]
  rw [e0, e1] at h
  exact h

theorem part_009_0 : RS5.BandZeros ((49474019174 : ℝ) / 65536) ((49482952378 : ℝ) / 65536) 254 := by
  have g0 := band_0072
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0073
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49474019174 : ℝ) / 65536) ((49482952378 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_009_0 <;> assumption
