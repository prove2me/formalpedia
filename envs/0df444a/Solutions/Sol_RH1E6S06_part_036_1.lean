-- Prove2me | solution 1 for RH1E6S06.part_036_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:43:46.45672+00:00
-- url     : https://prove2.me/submissions/86fd6a32-a6c0-459e-a418-b11cd1f514b8

import Definitions.Def_RH1E6S06_D036_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0290 : RS5.BandZeros ((27582277303 : ℝ) / 65536) ((27586968129 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0290.s0 RH1E6S06_0290.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0290.s0 RH1E6S06_0290.rest = RH1E6S06_0290.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0290.s0 :: RH1E6S06_0290.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0290.s0.t = ((27582277303 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0290.s0]
  have e1 : RH1E6S06_0290.sL.t = ((27586968129 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0290.sL]
  rw [e0, e1] at h
  exact h

theorem band_0291 : RS5.BandZeros ((27586968129 : ℝ) / 65536) ((27591709408 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0291.s0 RH1E6S06_0291.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0291.s0 RH1E6S06_0291.rest = RH1E6S06_0291.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0291.s0 :: RH1E6S06_0291.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0291.s0.t = ((27586968129 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0291.s0]
  have e1 : RH1E6S06_0291.sL.t = ((27591709408 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0291.sL]
  rw [e0, e1] at h
  exact h

theorem part_036_1 : RS5.BandZeros ((27582277303 : ℝ) / 65536) ((27591709408 : ℝ) / 65536) 254 := by
  have g0 := band_0290
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0291
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27582277303 : ℝ) / 65536) ((27591709408 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_036_1 <;> assumption
