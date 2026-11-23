-- Prove2me | solution 1 for RH1E6S14.part_075_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T06:47:06.601166+00:00
-- url     : https://prove2.me/submissions/1ce631c2-9278-44b4-b755-687a39467e25

import Definitions.Def_RH1E6S14_D075_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0606 : RS5.BandZeros ((55119098447 : ℝ) / 65536) ((55123537583 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0606.s0 RH1E6S14_0606.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0606.s0 RH1E6S14_0606.rest = RH1E6S14_0606.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0606.s0 :: RH1E6S14_0606.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0606.s0.t = ((55119098447 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0606.s0]
  have e1 : RH1E6S14_0606.sL.t = ((55123537583 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0606.sL]
  rw [e0, e1] at h
  exact h

theorem band_0607 : RS5.BandZeros ((55123537583 : ℝ) / 65536) ((55127954587 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0607.s0 RH1E6S14_0607.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0607.s0 RH1E6S14_0607.rest = RH1E6S14_0607.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0607.s0 :: RH1E6S14_0607.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0607.s0.t = ((55123537583 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0607.s0]
  have e1 : RH1E6S14_0607.sL.t = ((55127954587 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0607.sL]
  rw [e0, e1] at h
  exact h

theorem part_075_3 : RS5.BandZeros ((55119098447 : ℝ) / 65536) ((55127954587 : ℝ) / 65536) 254 := by
  have g0 := band_0606
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0607
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55119098447 : ℝ) / 65536) ((55127954587 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_075_3 <;> assumption
