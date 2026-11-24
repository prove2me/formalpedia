-- Prove2me | solution 1 for RH1E6S17.part_056_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:48:10.508106+00:00
-- url     : https://prove2.me/submissions/fcebbd33-257e-4ff0-a117-a04aea49cde2

import Definitions.Def_RH1E6S17_D056_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0454 : RS5.BandZeros ((64247308433 : ℝ) / 65536) ((64251673151 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0454.s0 RH1E6S17_0454.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0454.s0 RH1E6S17_0454.rest = RH1E6S17_0454.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0454.s0 :: RH1E6S17_0454.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0454.s0.t = ((64247308433 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0454.s0]
  have e1 : RH1E6S17_0454.sL.t = ((64251673151 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0454.sL]
  rw [e0, e1] at h
  exact h

theorem band_0455 : RS5.BandZeros ((64251673151 : ℝ) / 65536) ((64256055062 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0455.s0 RH1E6S17_0455.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0455.s0 RH1E6S17_0455.rest = RH1E6S17_0455.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0455.s0 :: RH1E6S17_0455.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0455.s0.t = ((64251673151 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0455.s0]
  have e1 : RH1E6S17_0455.sL.t = ((64256055062 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0455.sL]
  rw [e0, e1] at h
  exact h

theorem part_056_3 : RS5.BandZeros ((64247308433 : ℝ) / 65536) ((64256055062 : ℝ) / 65536) 254 := by
  have g0 := band_0454
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0455
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64247308433 : ℝ) / 65536) ((64256055062 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_056_3 <;> assumption
