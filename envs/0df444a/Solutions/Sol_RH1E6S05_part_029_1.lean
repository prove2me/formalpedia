-- Prove2me | solution 1 for RH1E6S05.part_029_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T13:13:52.86627+00:00
-- url     : https://prove2.me/submissions/e52c770a-f2a2-4353-8f2f-f8fc1f37625b

import Definitions.Def_RH1E6S05_D029_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0234 : RS5.BandZeros ((24054955777 : ℝ) / 65536) ((24059739287 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0234.s0 RH1E6S05_0234.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0234.s0 RH1E6S05_0234.rest = RH1E6S05_0234.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0234.s0 :: RH1E6S05_0234.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0234.s0.t = ((24054955777 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0234.s0]
  have e1 : RH1E6S05_0234.sL.t = ((24059739287 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0234.sL]
  rw [e0, e1] at h
  exact h

theorem band_0235 : RS5.BandZeros ((24059739287 : ℝ) / 65536) ((24064494573 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0235.s0 RH1E6S05_0235.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0235.s0 RH1E6S05_0235.rest = RH1E6S05_0235.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0235.s0 :: RH1E6S05_0235.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0235.s0.t = ((24059739287 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0235.s0]
  have e1 : RH1E6S05_0235.sL.t = ((24064494573 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0235.sL]
  rw [e0, e1] at h
  exact h

theorem part_029_1 : RS5.BandZeros ((24054955777 : ℝ) / 65536) ((24064494573 : ℝ) / 65536) 254 := by
  have g0 := band_0234
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0235
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((24054955777 : ℝ) / 65536) ((24064494573 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_029_1 <;> assumption
