-- Prove2me | solution 1 for RH1E6S13.part_036_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T22:31:22.727935+00:00
-- url     : https://prove2.me/submissions/7b701f8e-d1f2-47b7-86a1-bc23e2131f1d

import Definitions.Def_RH1E6S13_D036_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0288 : RS5.BandZeros ((50438946278 : ℝ) / 65536) ((50443418713 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0288.s0 RH1E6S13_0288.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0288.s0 RH1E6S13_0288.rest = RH1E6S13_0288.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0288.s0 :: RH1E6S13_0288.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0288.s0.t = ((50438946278 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0288.s0]
  have e1 : RH1E6S13_0288.sL.t = ((50443418713 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0288.sL]
  rw [e0, e1] at h
  exact h

theorem band_0289 : RS5.BandZeros ((50443418713 : ℝ) / 65536) ((50447873542 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0289.s0 RH1E6S13_0289.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0289.s0 RH1E6S13_0289.rest = RH1E6S13_0289.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0289.s0 :: RH1E6S13_0289.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0289.s0.t = ((50443418713 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0289.s0]
  have e1 : RH1E6S13_0289.sL.t = ((50447873542 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0289.sL]
  rw [e0, e1] at h
  exact h

theorem part_036_0 : RS5.BandZeros ((50438946278 : ℝ) / 65536) ((50447873542 : ℝ) / 65536) 254 := by
  have g0 := band_0288
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0289
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50438946278 : ℝ) / 65536) ((50447873542 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_036_0 <;> assumption
