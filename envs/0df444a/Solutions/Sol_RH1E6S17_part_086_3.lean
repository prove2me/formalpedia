-- Prove2me | solution 1 for RH1E6S17.part_086_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:24:42.528791+00:00
-- url     : https://prove2.me/submissions/16fd9376-8a16-41ee-bab6-a82927bb3be4

import Definitions.Def_RH1E6S17_D086_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0694 : RS5.BandZeros ((65296189154 : ℝ) / 65536) ((65300547970 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0694.s0 RH1E6S17_0694.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0694.s0 RH1E6S17_0694.rest = RH1E6S17_0694.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0694.s0 :: RH1E6S17_0694.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0694.s0.t = ((65296189154 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0694.s0]
  have e1 : RH1E6S17_0694.sL.t = ((65300547970 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0694.sL]
  rw [e0, e1] at h
  exact h

theorem band_0695 : RS5.BandZeros ((65300547970 : ℝ) / 65536) ((65304915358 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0695.s0 RH1E6S17_0695.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0695.s0 RH1E6S17_0695.rest = RH1E6S17_0695.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0695.s0 :: RH1E6S17_0695.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0695.s0.t = ((65300547970 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0695.s0]
  have e1 : RH1E6S17_0695.sL.t = ((65304915358 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0695.sL]
  rw [e0, e1] at h
  exact h

theorem part_086_3 : RS5.BandZeros ((65296189154 : ℝ) / 65536) ((65304915358 : ℝ) / 65536) 254 := by
  have g0 := band_0694
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0695
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65296189154 : ℝ) / 65536) ((65304915358 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_086_3 <;> assumption
