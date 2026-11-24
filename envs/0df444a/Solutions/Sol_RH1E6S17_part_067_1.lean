-- Prove2me | solution 1 for RH1E6S17.part_067_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T23:20:29.097122+00:00
-- url     : https://prove2.me/submissions/ccb06ca7-9d8e-4d96-b049-6e4e230fab08

import Definitions.Def_RH1E6S17_D067_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0538 : RS5.BandZeros ((64614572720 : ℝ) / 65536) ((64618943964 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0538.s0 RH1E6S17_0538.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0538.s0 RH1E6S17_0538.rest = RH1E6S17_0538.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0538.s0 :: RH1E6S17_0538.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0538.s0.t = ((64614572720 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0538.s0]
  have e1 : RH1E6S17_0538.sL.t = ((64618943964 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0538.sL]
  rw [e0, e1] at h
  exact h

theorem band_0539 : RS5.BandZeros ((64618943964 : ℝ) / 65536) ((64623315182 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0539.s0 RH1E6S17_0539.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0539.s0 RH1E6S17_0539.rest = RH1E6S17_0539.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0539.s0 :: RH1E6S17_0539.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0539.s0.t = ((64618943964 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0539.s0]
  have e1 : RH1E6S17_0539.sL.t = ((64623315182 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0539.sL]
  rw [e0, e1] at h
  exact h

theorem part_067_1 : RS5.BandZeros ((64614572720 : ℝ) / 65536) ((64623315182 : ℝ) / 65536) 254 := by
  have g0 := band_0538
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0539
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64614572720 : ℝ) / 65536) ((64623315182 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_067_1 <;> assumption
