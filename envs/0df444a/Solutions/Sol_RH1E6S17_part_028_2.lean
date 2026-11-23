-- Prove2me | solution 1 for RH1E6S17.part_028_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T21:05:59.543425+00:00
-- url     : https://prove2.me/submissions/d7750798-e24e-41cf-8a61-80f1f059f187

import Definitions.Def_RH1E6S17_D028_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0228 : RS5.BandZeros ((63258276576 : ℝ) / 65536) ((63262672824 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0228.s0 RH1E6S17_0228.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0228.s0 RH1E6S17_0228.rest = RH1E6S17_0228.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0228.s0 :: RH1E6S17_0228.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0228.s0.t = ((63258276576 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0228.s0]
  have e1 : RH1E6S17_0228.sL.t = ((63262672824 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0228.sL]
  rw [e0, e1] at h
  exact h

theorem band_0229 : RS5.BandZeros ((63262672824 : ℝ) / 65536) ((63267043187 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0229.s0 RH1E6S17_0229.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0229.s0 RH1E6S17_0229.rest = RH1E6S17_0229.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0229.s0 :: RH1E6S17_0229.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0229.s0.t = ((63262672824 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0229.s0]
  have e1 : RH1E6S17_0229.sL.t = ((63267043187 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0229.sL]
  rw [e0, e1] at h
  exact h

theorem part_028_2 : RS5.BandZeros ((63258276576 : ℝ) / 65536) ((63267043187 : ℝ) / 65536) 254 := by
  have g0 := band_0228
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0229
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63258276576 : ℝ) / 65536) ((63267043187 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_028_2 <;> assumption
