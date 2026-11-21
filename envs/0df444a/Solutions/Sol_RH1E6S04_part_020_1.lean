-- Prove2me | solution 1 for RH1E6S04.part_020_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:08:12.602015+00:00
-- url     : https://prove2.me/submissions/a7fba527-9fc2-47a3-94f1-2d8bf3b067f8

import Definitions.Def_RH1E6S04_D020_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0162 : RS5.BandZeros ((20445711682 : ℝ) / 65536) ((20450538540 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0162.s0 RH1E6S04_0162.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0162.s0 RH1E6S04_0162.rest = RH1E6S04_0162.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0162.s0 :: RH1E6S04_0162.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0162.s0.t = ((20445711682 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0162.s0]
  have e1 : RH1E6S04_0162.sL.t = ((20450538540 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0162.sL]
  rw [e0, e1] at h
  exact h

theorem band_0163 : RS5.BandZeros ((20450538540 : ℝ) / 65536) ((20455384334 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0163.s0 RH1E6S04_0163.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0163.s0 RH1E6S04_0163.rest = RH1E6S04_0163.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0163.s0 :: RH1E6S04_0163.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0163.s0.t = ((20450538540 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0163.s0]
  have e1 : RH1E6S04_0163.sL.t = ((20455384334 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0163.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_1 : RS5.BandZeros ((20445711682 : ℝ) / 65536) ((20455384334 : ℝ) / 65536) 254 := by
  have g0 := band_0162
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0163
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20445711682 : ℝ) / 65536) ((20455384334 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_020_1 <;> assumption
