-- Prove2me | solution 1 for RH1E6S07.part_030_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T00:21:05.358666+00:00
-- url     : https://prove2.me/submissions/7a67579c-a939-4e91-8564-2f52fcbdb1a8

import Definitions.Def_RH1E6S07_D030_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0240 : RS5.BandZeros ((30612015379 : ℝ) / 65536) ((30616689351 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0240.s0 RH1E6S07_0240.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0240.s0 RH1E6S07_0240.rest = RH1E6S07_0240.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0240.s0 :: RH1E6S07_0240.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0240.s0.t = ((30612015379 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0240.s0]
  have e1 : RH1E6S07_0240.sL.t = ((30616689351 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0240.sL]
  rw [e0, e1] at h
  exact h

theorem band_0241 : RS5.BandZeros ((30616689351 : ℝ) / 65536) ((30621348750 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0241.s0 RH1E6S07_0241.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0241.s0 RH1E6S07_0241.rest = RH1E6S07_0241.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0241.s0 :: RH1E6S07_0241.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0241.s0.t = ((30616689351 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0241.s0]
  have e1 : RH1E6S07_0241.sL.t = ((30621348750 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0241.sL]
  rw [e0, e1] at h
  exact h

theorem part_030_0 : RS5.BandZeros ((30612015379 : ℝ) / 65536) ((30621348750 : ℝ) / 65536) 254 := by
  have g0 := band_0240
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0241
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30612015379 : ℝ) / 65536) ((30621348750 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_030_0 <;> assumption
