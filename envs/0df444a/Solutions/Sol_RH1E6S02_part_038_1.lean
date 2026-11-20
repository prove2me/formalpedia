-- Prove2me | solution 1 for RH1E6S02.part_038_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:29:53.776909+00:00
-- url     : https://prove2.me/submissions/43c8e2d8-4201-4d15-a56c-059e607560d0

import Definitions.Def_RH1E6S02_D038_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0306 : RS5.BandZeros ((14642263125 : ℝ) / 65536) ((14647250162 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0306.s0 RH1E6S02_0306.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0306.s0 RH1E6S02_0306.rest = RH1E6S02_0306.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0306.s0 :: RH1E6S02_0306.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0306.s0.t = ((14642263125 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0306.s0]
  have e1 : RH1E6S02_0306.sL.t = ((14647250162 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0306.sL]
  rw [e0, e1] at h
  exact h

theorem band_0307 : RS5.BandZeros ((14647250162 : ℝ) / 65536) ((14652250263 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0307.s0 RH1E6S02_0307.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0307.s0 RH1E6S02_0307.rest = RH1E6S02_0307.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0307.s0 :: RH1E6S02_0307.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0307.s0.t = ((14647250162 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0307.s0]
  have e1 : RH1E6S02_0307.sL.t = ((14652250263 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0307.sL]
  rw [e0, e1] at h
  exact h

theorem part_038_1 : RS5.BandZeros ((14642263125 : ℝ) / 65536) ((14652250263 : ℝ) / 65536) 254 := by
  have g0 := band_0306
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0307
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((14642263125 : ℝ) / 65536) ((14652250263 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_038_1 <;> assumption
