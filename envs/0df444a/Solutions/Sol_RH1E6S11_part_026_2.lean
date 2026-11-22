-- Prove2me | solution 1 for RH1E6S11.part_026_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T04:16:56.727968+00:00
-- url     : https://prove2.me/submissions/cc7ca628-8276-4cef-9b23-e0b1732231dc

import Definitions.Def_RH1E6S11_D026_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0212 : RS5.BandZeros ((43557611370 : ℝ) / 65536) ((43562131608 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0212.s0 RH1E6S11_0212.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0212.s0 RH1E6S11_0212.rest = RH1E6S11_0212.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0212.s0 :: RH1E6S11_0212.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0212.s0.t = ((43557611370 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0212.s0]
  have e1 : RH1E6S11_0212.sL.t = ((43562131608 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0212.sL]
  rw [e0, e1] at h
  exact h

theorem band_0213 : RS5.BandZeros ((43562131608 : ℝ) / 65536) ((43566651806 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0213.s0 RH1E6S11_0213.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0213.s0 RH1E6S11_0213.rest = RH1E6S11_0213.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0213.s0 :: RH1E6S11_0213.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0213.s0.t = ((43562131608 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0213.s0]
  have e1 : RH1E6S11_0213.sL.t = ((43566651806 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0213.sL]
  rw [e0, e1] at h
  exact h

theorem part_026_2 : RS5.BandZeros ((43557611370 : ℝ) / 65536) ((43566651806 : ℝ) / 65536) 254 := by
  have g0 := band_0212
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0213
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43557611370 : ℝ) / 65536) ((43566651806 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_026_2 <;> assumption
