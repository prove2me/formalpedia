-- Prove2me | solution 1 for RH1E6S11.part_014_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:40:30.308198+00:00
-- url     : https://prove2.me/submissions/541c36a4-a8da-46ce-a105-a54505147125

import Definitions.Def_RH1E6S11_D014_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0114 : RS5.BandZeros ((43114448320 : ℝ) / 65536) ((43118945839 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0114.s0 RH1E6S11_0114.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0114.s0 RH1E6S11_0114.rest = RH1E6S11_0114.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0114.s0 :: RH1E6S11_0114.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0114.s0.t = ((43114448320 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0114.s0]
  have e1 : RH1E6S11_0114.sL.t = ((43118945839 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0114.sL]
  rw [e0, e1] at h
  exact h

theorem band_0115 : RS5.BandZeros ((43118945839 : ℝ) / 65536) ((43123478941 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0115.s0 RH1E6S11_0115.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0115.s0 RH1E6S11_0115.rest = RH1E6S11_0115.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0115.s0 :: RH1E6S11_0115.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0115.s0.t = ((43118945839 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0115.s0]
  have e1 : RH1E6S11_0115.sL.t = ((43123478941 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0115.sL]
  rw [e0, e1] at h
  exact h

theorem part_014_1 : RS5.BandZeros ((43114448320 : ℝ) / 65536) ((43123478941 : ℝ) / 65536) 254 := by
  have g0 := band_0114
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0115
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43114448320 : ℝ) / 65536) ((43123478941 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_014_1 <;> assumption
