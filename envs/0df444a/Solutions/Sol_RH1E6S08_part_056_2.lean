-- Prove2me | solution 1 for RH1E6S08.part_056_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T06:40:52.058404+00:00
-- url     : https://prove2.me/submissions/266056f0-a680-43a2-a76f-ab37e6118cbb

import Definitions.Def_RH1E6S08_D056_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0452 : RS5.BandZeros ((34856947874 : ℝ) / 65536) ((34861547807 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0452.s0 RH1E6S08_0452.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0452.s0 RH1E6S08_0452.rest = RH1E6S08_0452.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0452.s0 :: RH1E6S08_0452.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0452.s0.t = ((34856947874 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0452.s0]
  have e1 : RH1E6S08_0452.sL.t = ((34861547807 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0452.sL]
  rw [e0, e1] at h
  exact h

theorem band_0453 : RS5.BandZeros ((34861547807 : ℝ) / 65536) ((34866138614 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0453.s0 RH1E6S08_0453.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0453.s0 RH1E6S08_0453.rest = RH1E6S08_0453.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0453.s0 :: RH1E6S08_0453.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0453.s0.t = ((34861547807 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0453.s0]
  have e1 : RH1E6S08_0453.sL.t = ((34866138614 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0453.sL]
  rw [e0, e1] at h
  exact h

theorem part_056_2 : RS5.BandZeros ((34856947874 : ℝ) / 65536) ((34866138614 : ℝ) / 65536) 254 := by
  have g0 := band_0452
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0453
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((34856947874 : ℝ) / 65536) ((34866138614 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_056_2 <;> assumption
