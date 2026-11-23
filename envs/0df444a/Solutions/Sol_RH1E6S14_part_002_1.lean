-- Prove2me | solution 1 for RH1E6S14.part_002_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:33:57.810812+00:00
-- url     : https://prove2.me/submissions/77ed7587-1a9b-4b62-a713-0ace8af8ed29

import Definitions.Def_RH1E6S14_D002_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0018 : RS5.BandZeros ((52508882873 : ℝ) / 65536) ((52513331252 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0018.s0 RH1E6S14_0018.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0018.s0 RH1E6S14_0018.rest = RH1E6S14_0018.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0018.s0 :: RH1E6S14_0018.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0018.s0.t = ((52508882873 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0018.s0]
  have e1 : RH1E6S14_0018.sL.t = ((52513331252 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0018.sL]
  rw [e0, e1] at h
  exact h

theorem band_0019 : RS5.BandZeros ((52513331252 : ℝ) / 65536) ((52517770843 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0019.s0 RH1E6S14_0019.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0019.s0 RH1E6S14_0019.rest = RH1E6S14_0019.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0019.s0 :: RH1E6S14_0019.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0019.s0.t = ((52513331252 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0019.s0]
  have e1 : RH1E6S14_0019.sL.t = ((52517770843 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0019.sL]
  rw [e0, e1] at h
  exact h

theorem part_002_1 : RS5.BandZeros ((52508882873 : ℝ) / 65536) ((52517770843 : ℝ) / 65536) 254 := by
  have g0 := band_0018
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0019
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((52508882873 : ℝ) / 65536) ((52517770843 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_002_1 <;> assumption
