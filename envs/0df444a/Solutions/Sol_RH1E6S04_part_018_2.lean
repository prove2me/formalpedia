-- Prove2me | solution 1 for RH1E6S04.part_018_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:05:38.317391+00:00
-- url     : https://prove2.me/submissions/2c2e975c-4f81-4a4d-bac1-ed69320554fa

import Definitions.Def_RH1E6S04_D018_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0148 : RS5.BandZeros ((20378000776 : ℝ) / 65536) ((20382838639 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0148.s0 RH1E6S04_0148.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0148.s0 RH1E6S04_0148.rest = RH1E6S04_0148.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0148.s0 :: RH1E6S04_0148.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0148.s0.t = ((20378000776 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0148.s0]
  have e1 : RH1E6S04_0148.sL.t = ((20382838639 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0148.sL]
  rw [e0, e1] at h
  exact h

theorem band_0149 : RS5.BandZeros ((20382838639 : ℝ) / 65536) ((20387676396 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0149.s0 RH1E6S04_0149.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0149.s0 RH1E6S04_0149.rest = RH1E6S04_0149.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0149.s0 :: RH1E6S04_0149.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0149.s0.t = ((20382838639 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0149.s0]
  have e1 : RH1E6S04_0149.sL.t = ((20387676396 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0149.sL]
  rw [e0, e1] at h
  exact h

theorem part_018_2 : RS5.BandZeros ((20378000776 : ℝ) / 65536) ((20387676396 : ℝ) / 65536) 254 := by
  have g0 := band_0148
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0149
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20378000776 : ℝ) / 65536) ((20387676396 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_018_2 <;> assumption
