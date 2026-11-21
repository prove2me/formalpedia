-- Prove2me | solution 1 for RH1E6S07.part_005_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T23:06:40.773001+00:00
-- url     : https://prove2.me/submissions/72743a66-601a-4df2-b205-df01e56ee5e2

import Definitions.Def_RH1E6S07_D005_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0040 : RS5.BandZeros ((29678255590 : ℝ) / 65536) ((29682923865 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0040.s0 RH1E6S07_0040.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0040.s0 RH1E6S07_0040.rest = RH1E6S07_0040.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0040.s0 :: RH1E6S07_0040.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0040.s0.t = ((29678255590 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0040.s0]
  have e1 : RH1E6S07_0040.sL.t = ((29682923865 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0040.sL]
  rw [e0, e1] at h
  exact h

theorem band_0041 : RS5.BandZeros ((29682923865 : ℝ) / 65536) ((29687621058 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0041.s0 RH1E6S07_0041.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0041.s0 RH1E6S07_0041.rest = RH1E6S07_0041.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0041.s0 :: RH1E6S07_0041.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0041.s0.t = ((29682923865 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0041.s0]
  have e1 : RH1E6S07_0041.sL.t = ((29687621058 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0041.sL]
  rw [e0, e1] at h
  exact h

theorem part_005_0 : RS5.BandZeros ((29678255590 : ℝ) / 65536) ((29687621058 : ℝ) / 65536) 254 := by
  have g0 := band_0040
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0041
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((29678255590 : ℝ) / 65536) ((29687621058 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_005_0 <;> assumption
