-- Prove2me | solution 1 for RH1E6S13.part_024_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T21:35:38.850526+00:00
-- url     : https://prove2.me/submissions/8d446b09-9acb-49a6-8c0d-59b4424df6e0

import Definitions.Def_RH1E6S13_D024_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0192 : RS5.BandZeros ((50010296033 : ℝ) / 65536) ((50014745349 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0192.s0 RH1E6S13_0192.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0192.s0 RH1E6S13_0192.rest = RH1E6S13_0192.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0192.s0 :: RH1E6S13_0192.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0192.s0.t = ((50010296033 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0192.s0]
  have e1 : RH1E6S13_0192.sL.t = ((50014745349 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0192.sL]
  rw [e0, e1] at h
  exact h

theorem band_0193 : RS5.BandZeros ((50014745349 : ℝ) / 65536) ((50019229804 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0193.s0 RH1E6S13_0193.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0193.s0 RH1E6S13_0193.rest = RH1E6S13_0193.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0193.s0 :: RH1E6S13_0193.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0193.s0.t = ((50014745349 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0193.s0]
  have e1 : RH1E6S13_0193.sL.t = ((50019229804 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0193.sL]
  rw [e0, e1] at h
  exact h

theorem part_024_0 : RS5.BandZeros ((50010296033 : ℝ) / 65536) ((50019229804 : ℝ) / 65536) 254 := by
  have g0 := band_0192
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0193
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50010296033 : ℝ) / 65536) ((50019229804 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_024_0 <;> assumption
