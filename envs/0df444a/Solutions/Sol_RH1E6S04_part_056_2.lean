-- Prove2me | solution 1 for RH1E6S04.part_056_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:32:48.025288+00:00
-- url     : https://prove2.me/submissions/7b44c0f4-16c5-4867-941f-3fc2f8d09ffe

import Definitions.Def_RH1E6S04_D056_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0452 : RS5.BandZeros ((21843971570 : ℝ) / 65536) ((21848778544 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0452.s0 RH1E6S04_0452.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0452.s0 RH1E6S04_0452.rest = RH1E6S04_0452.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0452.s0 :: RH1E6S04_0452.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0452.s0.t = ((21843971570 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0452.s0]
  have e1 : RH1E6S04_0452.sL.t = ((21848778544 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0452.sL]
  rw [e0, e1] at h
  exact h

theorem band_0453 : RS5.BandZeros ((21848778544 : ℝ) / 65536) ((21853585421 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0453.s0 RH1E6S04_0453.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0453.s0 RH1E6S04_0453.rest = RH1E6S04_0453.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0453.s0 :: RH1E6S04_0453.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0453.s0.t = ((21848778544 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0453.s0]
  have e1 : RH1E6S04_0453.sL.t = ((21853585421 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0453.sL]
  rw [e0, e1] at h
  exact h

theorem part_056_2 : RS5.BandZeros ((21843971570 : ℝ) / 65536) ((21853585421 : ℝ) / 65536) 254 := by
  have g0 := band_0452
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0453
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((21843971570 : ℝ) / 65536) ((21853585421 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_056_2 <;> assumption
