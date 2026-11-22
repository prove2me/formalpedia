-- Prove2me | solution 1 for RH1E6S13.part_010_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T19:22:02.211082+00:00
-- url     : https://prove2.me/submissions/db0659de-3d12-4299-8a40-cce4785a5691

import Definitions.Def_RH1E6S13_D010_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0084 : RS5.BandZeros ((49527651533 : ℝ) / 65536) ((49532148540 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0084.s0 RH1E6S13_0084.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0084.s0 RH1E6S13_0084.rest = RH1E6S13_0084.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0084.s0 :: RH1E6S13_0084.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0084.s0.t = ((49527651533 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0084.s0]
  have e1 : RH1E6S13_0084.sL.t = ((49532148540 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0084.sL]
  rw [e0, e1] at h
  exact h

theorem band_0085 : RS5.BandZeros ((49532148540 : ℝ) / 65536) ((49536601510 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0085.s0 RH1E6S13_0085.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0085.s0 RH1E6S13_0085.rest = RH1E6S13_0085.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0085.s0 :: RH1E6S13_0085.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0085.s0.t = ((49532148540 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0085.s0]
  have e1 : RH1E6S13_0085.sL.t = ((49536601510 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0085.sL]
  rw [e0, e1] at h
  exact h

theorem part_010_2 : RS5.BandZeros ((49527651533 : ℝ) / 65536) ((49536601510 : ℝ) / 65536) 254 := by
  have g0 := band_0084
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0085
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49527651533 : ℝ) / 65536) ((49536601510 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_010_2 <;> assumption
