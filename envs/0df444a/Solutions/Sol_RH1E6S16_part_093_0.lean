-- Prove2me | solution 1 for RH1E6S16.part_093_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:31:22.279873+00:00
-- url     : https://prove2.me/submissions/b98587cb-1633-4e22-a078-911eac0e1ddb

import Definitions.Def_RH1E6S16_D093_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0744 : RS5.BandZeros ((62252083202 : ℝ) / 65536) ((62256482221 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0744.s0 RH1E6S16_0744.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0744.s0 RH1E6S16_0744.rest = RH1E6S16_0744.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0744.s0 :: RH1E6S16_0744.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0744.s0.t = ((62252083202 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0744.s0]
  have e1 : RH1E6S16_0744.sL.t = ((62256482221 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0744.sL]
  rw [e0, e1] at h
  exact h

theorem band_0745 : RS5.BandZeros ((62256482221 : ℝ) / 65536) ((62259200000 : ℝ) / 65536) 79 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0745.s0 RH1E6S16_0745.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0745.s0 RH1E6S16_0745.rest = RH1E6S16_0745.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0745.s0 :: RH1E6S16_0745.rest) = 79 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0745.s0.t = ((62256482221 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0745.s0]
  have e1 : RH1E6S16_0745.sL.t = ((62259200000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0745.sL]
  rw [e0, e1] at h
  exact h

theorem part_093_0 : RS5.BandZeros ((62252083202 : ℝ) / 65536) ((62259200000 : ℝ) / 65536) 206 := by
  have g0 := band_0744
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0745
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((62252083202 : ℝ) / 65536) ((62259200000 : ℝ) / 65536) 206 := by
  apply RH1E6S16.part_093_0 <;> assumption
