-- Prove2me | solution 1 for RH1E6S14.part_075_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T06:47:04.546376+00:00
-- url     : https://prove2.me/submissions/a0eecc64-f64c-4cce-8873-86eb067cb0f6

import Definitions.Def_RH1E6S14_D075_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0604 : RS5.BandZeros ((55110234936 : ℝ) / 65536) ((55114670856 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0604.s0 RH1E6S14_0604.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0604.s0 RH1E6S14_0604.rest = RH1E6S14_0604.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0604.s0 :: RH1E6S14_0604.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0604.s0.t = ((55110234936 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0604.s0]
  have e1 : RH1E6S14_0604.sL.t = ((55114670856 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0604.sL]
  rw [e0, e1] at h
  exact h

theorem band_0605 : RS5.BandZeros ((55114670856 : ℝ) / 65536) ((55119098447 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0605.s0 RH1E6S14_0605.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0605.s0 RH1E6S14_0605.rest = RH1E6S14_0605.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0605.s0 :: RH1E6S14_0605.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0605.s0.t = ((55114670856 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0605.s0]
  have e1 : RH1E6S14_0605.sL.t = ((55119098447 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0605.sL]
  rw [e0, e1] at h
  exact h

theorem part_075_2 : RS5.BandZeros ((55110234936 : ℝ) / 65536) ((55119098447 : ℝ) / 65536) 254 := by
  have g0 := band_0604
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0605
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55110234936 : ℝ) / 65536) ((55119098447 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_075_2 <;> assumption
