-- Prove2me | solution 1 for RH1E6S13.part_023_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T21:30:08.280663+00:00
-- url     : https://prove2.me/submissions/33648a9f-2fb0-4764-8f81-28c0ca6e7ff5

import Definitions.Def_RH1E6S13_D023_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0186 : RS5.BandZeros ((49983485107 : ℝ) / 65536) ((49987952214 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0186.s0 RH1E6S13_0186.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0186.s0 RH1E6S13_0186.rest = RH1E6S13_0186.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0186.s0 :: RH1E6S13_0186.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0186.s0.t = ((49983485107 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0186.s0]
  have e1 : RH1E6S13_0186.sL.t = ((49987952214 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0186.sL]
  rw [e0, e1] at h
  exact h

theorem band_0187 : RS5.BandZeros ((49987952214 : ℝ) / 65536) ((49992428081 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0187.s0 RH1E6S13_0187.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0187.s0 RH1E6S13_0187.rest = RH1E6S13_0187.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0187.s0 :: RH1E6S13_0187.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0187.s0.t = ((49987952214 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0187.s0]
  have e1 : RH1E6S13_0187.sL.t = ((49992428081 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0187.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_1 : RS5.BandZeros ((49983485107 : ℝ) / 65536) ((49992428081 : ℝ) / 65536) 254 := by
  have g0 := band_0186
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0187
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49983485107 : ℝ) / 65536) ((49992428081 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_023_1 <;> assumption
