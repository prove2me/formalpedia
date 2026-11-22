-- Prove2me | solution 1 for RH1E6S11.part_015_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:45:52.331127+00:00
-- url     : https://prove2.me/submissions/9c8fc0c8-6e2a-4a69-8897-e01661a095ab

import Definitions.Def_RH1E6S11_D015_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0122 : RS5.BandZeros ((43150623255 : ℝ) / 65536) ((43155138259 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0122.s0 RH1E6S11_0122.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0122.s0 RH1E6S11_0122.rest = RH1E6S11_0122.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0122.s0 :: RH1E6S11_0122.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0122.s0.t = ((43150623255 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0122.s0]
  have e1 : RH1E6S11_0122.sL.t = ((43155138259 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0122.sL]
  rw [e0, e1] at h
  exact h

theorem band_0123 : RS5.BandZeros ((43155138259 : ℝ) / 65536) ((43159679937 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0123.s0 RH1E6S11_0123.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0123.s0 RH1E6S11_0123.rest = RH1E6S11_0123.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0123.s0 :: RH1E6S11_0123.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0123.s0.t = ((43155138259 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0123.s0]
  have e1 : RH1E6S11_0123.sL.t = ((43159679937 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0123.sL]
  rw [e0, e1] at h
  exact h

theorem part_015_1 : RS5.BandZeros ((43150623255 : ℝ) / 65536) ((43159679937 : ℝ) / 65536) 254 := by
  have g0 := band_0122
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0123
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43150623255 : ℝ) / 65536) ((43159679937 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_015_1 <;> assumption
