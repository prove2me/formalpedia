-- Prove2me | solution 1 for RH1E6S13.part_007_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T19:16:11.177811+00:00
-- url     : https://prove2.me/submissions/ca9f3d02-c8a1-40b5-9cf1-c2e8b7670743

import Definitions.Def_RH1E6S13_D007_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0062 : RS5.BandZeros ((49429307074 : ℝ) / 65536) ((49433760836 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0062.s0 RH1E6S13_0062.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0062.s0 RH1E6S13_0062.rest = RH1E6S13_0062.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0062.s0 :: RH1E6S13_0062.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0062.s0.t = ((49429307074 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0062.s0]
  have e1 : RH1E6S13_0062.sL.t = ((49433760836 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0062.sL]
  rw [e0, e1] at h
  exact h

theorem band_0063 : RS5.BandZeros ((49433760836 : ℝ) / 65536) ((49438240969 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0063.s0 RH1E6S13_0063.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0063.s0 RH1E6S13_0063.rest = RH1E6S13_0063.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0063.s0 :: RH1E6S13_0063.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0063.s0.t = ((49433760836 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0063.s0]
  have e1 : RH1E6S13_0063.sL.t = ((49438240969 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0063.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_3 : RS5.BandZeros ((49429307074 : ℝ) / 65536) ((49438240969 : ℝ) / 65536) 254 := by
  have g0 := band_0062
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0063
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49429307074 : ℝ) / 65536) ((49438240969 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_007_3 <;> assumption
