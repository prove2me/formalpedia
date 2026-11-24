-- Prove2me | solution 1 for RH1E6S17.part_074_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T23:46:23.798608+00:00
-- url     : https://prove2.me/submissions/defd98d4-c385-46ef-880b-cd5b335c28d3

import Definitions.Def_RH1E6S17_D074_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0598 : RS5.BandZeros ((64876812248 : ℝ) / 65536) ((64881164808 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0598.s0 RH1E6S17_0598.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0598.s0 RH1E6S17_0598.rest = RH1E6S17_0598.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0598.s0 :: RH1E6S17_0598.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0598.s0.t = ((64876812248 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0598.s0]
  have e1 : RH1E6S17_0598.sL.t = ((64881164808 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0598.sL]
  rw [e0, e1] at h
  exact h

theorem band_0599 : RS5.BandZeros ((64881164808 : ℝ) / 65536) ((64885543150 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0599.s0 RH1E6S17_0599.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0599.s0 RH1E6S17_0599.rest = RH1E6S17_0599.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0599.s0 :: RH1E6S17_0599.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0599.s0.t = ((64881164808 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0599.s0]
  have e1 : RH1E6S17_0599.sL.t = ((64885543150 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0599.sL]
  rw [e0, e1] at h
  exact h

theorem part_074_3 : RS5.BandZeros ((64876812248 : ℝ) / 65536) ((64885543150 : ℝ) / 65536) 254 := by
  have g0 := band_0598
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0599
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64876812248 : ℝ) / 65536) ((64885543150 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_074_3 <;> assumption
