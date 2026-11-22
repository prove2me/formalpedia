-- Prove2me | solution 1 for RH1E6S13.part_039_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T22:50:35.052944+00:00
-- url     : https://prove2.me/submissions/9e6e28e3-d8fa-4046-8e18-a5ce27dd5470

import Definitions.Def_RH1E6S13_D039_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0318 : RS5.BandZeros ((50572858663 : ℝ) / 65536) ((50577303733 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0318.s0 RH1E6S13_0318.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0318.s0 RH1E6S13_0318.rest = RH1E6S13_0318.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0318.s0 :: RH1E6S13_0318.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0318.s0.t = ((50572858663 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0318.s0]
  have e1 : RH1E6S13_0318.sL.t = ((50577303733 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0318.sL]
  rw [e0, e1] at h
  exact h

theorem band_0319 : RS5.BandZeros ((50577303733 : ℝ) / 65536) ((50581775123 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0319.s0 RH1E6S13_0319.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0319.s0 RH1E6S13_0319.rest = RH1E6S13_0319.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0319.s0 :: RH1E6S13_0319.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0319.s0.t = ((50577303733 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0319.s0]
  have e1 : RH1E6S13_0319.sL.t = ((50581775123 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0319.sL]
  rw [e0, e1] at h
  exact h

theorem part_039_3 : RS5.BandZeros ((50572858663 : ℝ) / 65536) ((50581775123 : ℝ) / 65536) 254 := by
  have g0 := band_0318
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0319
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50572858663 : ℝ) / 65536) ((50581775123 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_039_3 <;> assumption
