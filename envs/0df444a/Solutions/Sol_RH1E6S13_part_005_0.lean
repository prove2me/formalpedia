-- Prove2me | solution 1 for RH1E6S13.part_005_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T18:00:15.283927+00:00
-- url     : https://prove2.me/submissions/1e27c011-9e35-40ce-b3d0-b89282ac32e4

import Definitions.Def_RH1E6S13_D005_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0040 : RS5.BandZeros ((49330910669 : ℝ) / 65536) ((49335391600 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0040.s0 RH1E6S13_0040.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0040.s0 RH1E6S13_0040.rest = RH1E6S13_0040.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0040.s0 :: RH1E6S13_0040.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0040.s0.t = ((49330910669 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0040.s0]
  have e1 : RH1E6S13_0040.sL.t = ((49335391600 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0040.sL]
  rw [e0, e1] at h
  exact h

theorem band_0041 : RS5.BandZeros ((49335391600 : ℝ) / 65536) ((49339854889 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0041.s0 RH1E6S13_0041.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0041.s0 RH1E6S13_0041.rest = RH1E6S13_0041.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0041.s0 :: RH1E6S13_0041.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0041.s0.t = ((49335391600 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0041.s0]
  have e1 : RH1E6S13_0041.sL.t = ((49339854889 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0041.sL]
  rw [e0, e1] at h
  exact h

theorem part_005_0 : RS5.BandZeros ((49330910669 : ℝ) / 65536) ((49339854889 : ℝ) / 65536) 254 := by
  have g0 := band_0040
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0041
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49330910669 : ℝ) / 65536) ((49339854889 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_005_0 <;> assumption
