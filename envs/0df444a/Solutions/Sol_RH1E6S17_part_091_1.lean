-- Prove2me | solution 1 for RH1E6S17.part_091_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:40:41.828201+00:00
-- url     : https://prove2.me/submissions/05381dd5-23f7-44c3-91a1-71a9d550294c

import Definitions.Def_RH1E6S17_D091_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0730 : RS5.BandZeros ((65453400656 : ℝ) / 65536) ((65457767192 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0730.s0 RH1E6S17_0730.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0730.s0 RH1E6S17_0730.rest = RH1E6S17_0730.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0730.s0 :: RH1E6S17_0730.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0730.s0.t = ((65453400656 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0730.s0]
  have e1 : RH1E6S17_0730.sL.t = ((65457767192 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0730.sL]
  rw [e0, e1] at h
  exact h

theorem band_0731 : RS5.BandZeros ((65457767192 : ℝ) / 65536) ((65462133704 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0731.s0 RH1E6S17_0731.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0731.s0 RH1E6S17_0731.rest = RH1E6S17_0731.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0731.s0 :: RH1E6S17_0731.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0731.s0.t = ((65457767192 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0731.s0]
  have e1 : RH1E6S17_0731.sL.t = ((65462133704 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0731.sL]
  rw [e0, e1] at h
  exact h

theorem part_091_1 : RS5.BandZeros ((65453400656 : ℝ) / 65536) ((65462133704 : ℝ) / 65536) 254 := by
  have g0 := band_0730
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0731
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65453400656 : ℝ) / 65536) ((65462133704 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_091_1 <;> assumption
