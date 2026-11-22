-- Prove2me | solution 1 for RH1E6S13.part_012_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T19:30:35.571698+00:00
-- url     : https://prove2.me/submissions/2306ff59-955f-43ee-8444-ceb93c95ba2b

import Definitions.Def_RH1E6S13_D012_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0100 : RS5.BandZeros ((49599203487 : ℝ) / 65536) ((49603655942 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0100.s0 RH1E6S13_0100.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0100.s0 RH1E6S13_0100.rest = RH1E6S13_0100.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0100.s0 :: RH1E6S13_0100.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0100.s0.t = ((49599203487 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0100.s0]
  have e1 : RH1E6S13_0100.sL.t = ((49603655942 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0100.sL]
  rw [e0, e1] at h
  exact h

theorem band_0101 : RS5.BandZeros ((49603655942 : ℝ) / 65536) ((49608143560 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0101.s0 RH1E6S13_0101.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0101.s0 RH1E6S13_0101.rest = RH1E6S13_0101.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0101.s0 :: RH1E6S13_0101.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0101.s0.t = ((49603655942 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0101.s0]
  have e1 : RH1E6S13_0101.sL.t = ((49608143560 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0101.sL]
  rw [e0, e1] at h
  exact h

theorem part_012_2 : RS5.BandZeros ((49599203487 : ℝ) / 65536) ((49608143560 : ℝ) / 65536) 254 := by
  have g0 := band_0100
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0101
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49599203487 : ℝ) / 65536) ((49608143560 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_012_2 <;> assumption
