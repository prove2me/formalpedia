-- Prove2me | solution 1 for RH1E6S14.part_075_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T06:47:02.525966+00:00
-- url     : https://prove2.me/submissions/3bfe2ed8-a8c6-4fa5-a53b-94478022ad7d

import Definitions.Def_RH1E6S14_D075_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0602 : RS5.BandZeros ((55101381994 : ℝ) / 65536) ((55105801788 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0602.s0 RH1E6S14_0602.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0602.s0 RH1E6S14_0602.rest = RH1E6S14_0602.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0602.s0 :: RH1E6S14_0602.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0602.s0.t = ((55101381994 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0602.s0]
  have e1 : RH1E6S14_0602.sL.t = ((55105801788 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0602.sL]
  rw [e0, e1] at h
  exact h

theorem band_0603 : RS5.BandZeros ((55105801788 : ℝ) / 65536) ((55110234936 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0603.s0 RH1E6S14_0603.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0603.s0 RH1E6S14_0603.rest = RH1E6S14_0603.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0603.s0 :: RH1E6S14_0603.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0603.s0.t = ((55105801788 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0603.s0]
  have e1 : RH1E6S14_0603.sL.t = ((55110234936 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0603.sL]
  rw [e0, e1] at h
  exact h

theorem part_075_1 : RS5.BandZeros ((55101381994 : ℝ) / 65536) ((55110234936 : ℝ) / 65536) 254 := by
  have g0 := band_0602
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0603
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55101381994 : ℝ) / 65536) ((55110234936 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_075_1 <;> assumption
