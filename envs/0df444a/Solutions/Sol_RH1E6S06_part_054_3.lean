-- Prove2me | solution 1 for RH1E6S06.part_054_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T19:54:13.903863+00:00
-- url     : https://prove2.me/submissions/1a44dea3-8bdd-434b-a3d4-1e114ccc395d

import Definitions.Def_RH1E6S06_D054_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0438 : RS5.BandZeros ((28277990049 : ℝ) / 65536) ((28282703640 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0438.s0 RH1E6S06_0438.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0438.s0 RH1E6S06_0438.rest = RH1E6S06_0438.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0438.s0 :: RH1E6S06_0438.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0438.s0.t = ((28277990049 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0438.s0]
  have e1 : RH1E6S06_0438.sL.t = ((28282703640 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0438.sL]
  rw [e0, e1] at h
  exact h

theorem band_0439 : RS5.BandZeros ((28282703640 : ℝ) / 65536) ((28287389887 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0439.s0 RH1E6S06_0439.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0439.s0 RH1E6S06_0439.rest = RH1E6S06_0439.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0439.s0 :: RH1E6S06_0439.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0439.s0.t = ((28282703640 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0439.s0]
  have e1 : RH1E6S06_0439.sL.t = ((28287389887 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0439.sL]
  rw [e0, e1] at h
  exact h

theorem part_054_3 : RS5.BandZeros ((28277990049 : ℝ) / 65536) ((28287389887 : ℝ) / 65536) 254 := by
  have g0 := band_0438
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0439
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28277990049 : ℝ) / 65536) ((28287389887 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_054_3 <;> assumption
