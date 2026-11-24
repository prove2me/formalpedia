-- Prove2me | solution 1 for RH1E6S17.part_051_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:29:11.737935+00:00
-- url     : https://prove2.me/submissions/57ff13b4-c488-491e-a307-38740e698e1e

import Definitions.Def_RH1E6S17_D051_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0414 : RS5.BandZeros ((64072354915 : ℝ) / 65536) ((64076729240 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0414.s0 RH1E6S17_0414.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0414.s0 RH1E6S17_0414.rest = RH1E6S17_0414.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0414.s0 :: RH1E6S17_0414.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0414.s0.t = ((64072354915 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0414.s0]
  have e1 : RH1E6S17_0414.sL.t = ((64076729240 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0414.sL]
  rw [e0, e1] at h
  exact h

theorem band_0415 : RS5.BandZeros ((64076729240 : ℝ) / 65536) ((64081086317 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0415.s0 RH1E6S17_0415.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0415.s0 RH1E6S17_0415.rest = RH1E6S17_0415.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0415.s0 :: RH1E6S17_0415.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0415.s0.t = ((64076729240 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0415.s0]
  have e1 : RH1E6S17_0415.sL.t = ((64081086317 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0415.sL]
  rw [e0, e1] at h
  exact h

theorem part_051_3 : RS5.BandZeros ((64072354915 : ℝ) / 65536) ((64081086317 : ℝ) / 65536) 254 := by
  have g0 := band_0414
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0415
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64072354915 : ℝ) / 65536) ((64081086317 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_051_3 <;> assumption
