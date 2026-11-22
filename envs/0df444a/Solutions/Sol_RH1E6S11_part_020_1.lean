-- Prove2me | solution 1 for RH1E6S11.part_020_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:59:54.427418+00:00
-- url     : https://prove2.me/submissions/5c860a26-4168-4778-9d18-abdf35d9b01d

import Definitions.Def_RH1E6S11_D020_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0162 : RS5.BandZeros ((43331547658 : ℝ) / 65536) ((43336069930 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0162.s0 RH1E6S11_0162.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0162.s0 RH1E6S11_0162.rest = RH1E6S11_0162.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0162.s0 :: RH1E6S11_0162.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0162.s0.t = ((43331547658 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0162.s0]
  have e1 : RH1E6S11_0162.sL.t = ((43336069930 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0162.sL]
  rw [e0, e1] at h
  exact h

theorem band_0163 : RS5.BandZeros ((43336069930 : ℝ) / 65536) ((43340592161 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0163.s0 RH1E6S11_0163.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0163.s0 RH1E6S11_0163.rest = RH1E6S11_0163.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0163.s0 :: RH1E6S11_0163.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0163.s0.t = ((43336069930 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0163.s0]
  have e1 : RH1E6S11_0163.sL.t = ((43340592161 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0163.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_1 : RS5.BandZeros ((43331547658 : ℝ) / 65536) ((43340592161 : ℝ) / 65536) 254 := by
  have g0 := band_0162
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0163
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43331547658 : ℝ) / 65536) ((43340592161 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_020_1 <;> assumption
