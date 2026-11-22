-- Prove2me | solution 1 for RH1E6S12.part_065_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T16:29:56.451092+00:00
-- url     : https://prove2.me/submissions/a46e0414-18bb-4e08-8b7a-ecdc744f7a65

import Definitions.Def_RH1E6S12_D065_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0526 : RS5.BandZeros ((48237128335 : ℝ) / 65536) ((48241598997 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0526.s0 RH1E6S12_0526.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0526.s0 RH1E6S12_0526.rest = RH1E6S12_0526.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0526.s0 :: RH1E6S12_0526.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0526.s0.t = ((48237128335 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0526.s0]
  have e1 : RH1E6S12_0526.sL.t = ((48241598997 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0526.sL]
  rw [e0, e1] at h
  exact h

theorem band_0527 : RS5.BandZeros ((48241598997 : ℝ) / 65536) ((48246088228 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0527.s0 RH1E6S12_0527.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0527.s0 RH1E6S12_0527.rest = RH1E6S12_0527.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0527.s0 :: RH1E6S12_0527.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0527.s0.t = ((48241598997 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0527.s0]
  have e1 : RH1E6S12_0527.sL.t = ((48246088228 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0527.sL]
  rw [e0, e1] at h
  exact h

theorem part_065_3 : RS5.BandZeros ((48237128335 : ℝ) / 65536) ((48246088228 : ℝ) / 65536) 254 := by
  have g0 := band_0526
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0527
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48237128335 : ℝ) / 65536) ((48246088228 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_065_3 <;> assumption
