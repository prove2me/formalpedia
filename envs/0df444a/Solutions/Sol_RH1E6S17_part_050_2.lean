-- Prove2me | solution 1 for RH1E6S17.part_050_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:25:59.569803+00:00
-- url     : https://prove2.me/submissions/5ba8d03e-7e0b-482c-9542-c4e8506d8287

import Definitions.Def_RH1E6S17_D050_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0404 : RS5.BandZeros ((64028601684 : ℝ) / 65536) ((64032976259 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0404.s0 RH1E6S17_0404.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0404.s0 RH1E6S17_0404.rest = RH1E6S17_0404.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0404.s0 :: RH1E6S17_0404.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0404.s0.t = ((64028601684 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0404.s0]
  have e1 : RH1E6S17_0404.sL.t = ((64032976259 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0404.sL]
  rw [e0, e1] at h
  exact h

theorem band_0405 : RS5.BandZeros ((64032976259 : ℝ) / 65536) ((64037359420 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0405.s0 RH1E6S17_0405.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0405.s0 RH1E6S17_0405.rest = RH1E6S17_0405.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0405.s0 :: RH1E6S17_0405.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0405.s0.t = ((64032976259 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0405.s0]
  have e1 : RH1E6S17_0405.sL.t = ((64037359420 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0405.sL]
  rw [e0, e1] at h
  exact h

theorem part_050_2 : RS5.BandZeros ((64028601684 : ℝ) / 65536) ((64037359420 : ℝ) / 65536) 254 := by
  have g0 := band_0404
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0405
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64028601684 : ℝ) / 65536) ((64037359420 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_050_2 <;> assumption
