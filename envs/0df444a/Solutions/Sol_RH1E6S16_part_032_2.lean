-- Prove2me | solution 1 for RH1E6S16.part_032_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:57:07.253805+00:00
-- url     : https://prove2.me/submissions/aef03064-c241-429d-8ace-9b7140e2c4d8

import Definitions.Def_RH1E6S16_D032_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0260 : RS5.BandZeros ((60126713988 : ℝ) / 65536) ((60131114331 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0260.s0 RH1E6S16_0260.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0260.s0 RH1E6S16_0260.rest = RH1E6S16_0260.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0260.s0 :: RH1E6S16_0260.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0260.s0.t = ((60126713988 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0260.s0]
  have e1 : RH1E6S16_0260.sL.t = ((60131114331 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0260.sL]
  rw [e0, e1] at h
  exact h

theorem band_0261 : RS5.BandZeros ((60131114331 : ℝ) / 65536) ((60135531670 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0261.s0 RH1E6S16_0261.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0261.s0 RH1E6S16_0261.rest = RH1E6S16_0261.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0261.s0 :: RH1E6S16_0261.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0261.s0.t = ((60131114331 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0261.s0]
  have e1 : RH1E6S16_0261.sL.t = ((60135531670 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0261.sL]
  rw [e0, e1] at h
  exact h

theorem part_032_2 : RS5.BandZeros ((60126713988 : ℝ) / 65536) ((60135531670 : ℝ) / 65536) 254 := by
  have g0 := band_0260
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0261
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60126713988 : ℝ) / 65536) ((60135531670 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_032_2 <;> assumption
