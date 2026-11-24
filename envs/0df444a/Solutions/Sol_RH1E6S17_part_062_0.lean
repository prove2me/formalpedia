-- Prove2me | solution 1 for RH1E6S17.part_062_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T23:04:10.815057+00:00
-- url     : https://prove2.me/submissions/3ac891a2-862b-49e9-988c-6cd79ed7d339

import Definitions.Def_RH1E6S17_D062_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0496 : RS5.BandZeros ((64430958152 : ℝ) / 65536) ((64435330435 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0496.s0 RH1E6S17_0496.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0496.s0 RH1E6S17_0496.rest = RH1E6S17_0496.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0496.s0 :: RH1E6S17_0496.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0496.s0.t = ((64430958152 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0496.s0]
  have e1 : RH1E6S17_0496.sL.t = ((64435330435 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0496.sL]
  rw [e0, e1] at h
  exact h

theorem band_0497 : RS5.BandZeros ((64435330435 : ℝ) / 65536) ((64439702694 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0497.s0 RH1E6S17_0497.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0497.s0 RH1E6S17_0497.rest = RH1E6S17_0497.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0497.s0 :: RH1E6S17_0497.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0497.s0.t = ((64435330435 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0497.s0]
  have e1 : RH1E6S17_0497.sL.t = ((64439702694 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0497.sL]
  rw [e0, e1] at h
  exact h

theorem part_062_0 : RS5.BandZeros ((64430958152 : ℝ) / 65536) ((64439702694 : ℝ) / 65536) 254 := by
  have g0 := band_0496
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0497
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64430958152 : ℝ) / 65536) ((64439702694 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_062_0 <;> assumption
