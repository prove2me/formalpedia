-- Prove2me | solution 1 for RH1E6S07.part_046_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:07:23.985645+00:00
-- url     : https://prove2.me/submissions/ad63c44e-3e34-4878-8960-78425689566f

import Definitions.Def_RH1E6S07_D046_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0370 : RS5.BandZeros ((31217614426 : ℝ) / 65536) ((31222245079 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0370.s0 RH1E6S07_0370.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0370.s0 RH1E6S07_0370.rest = RH1E6S07_0370.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0370.s0 :: RH1E6S07_0370.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0370.s0.t = ((31217614426 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0370.s0]
  have e1 : RH1E6S07_0370.sL.t = ((31222245079 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0370.sL]
  rw [e0, e1] at h
  exact h

theorem band_0371 : RS5.BandZeros ((31222245079 : ℝ) / 65536) ((31226909130 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0371.s0 RH1E6S07_0371.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0371.s0 RH1E6S07_0371.rest = RH1E6S07_0371.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0371.s0 :: RH1E6S07_0371.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0371.s0.t = ((31222245079 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0371.s0]
  have e1 : RH1E6S07_0371.sL.t = ((31226909130 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0371.sL]
  rw [e0, e1] at h
  exact h

theorem part_046_1 : RS5.BandZeros ((31217614426 : ℝ) / 65536) ((31226909130 : ℝ) / 65536) 254 := by
  have g0 := band_0370
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0371
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31217614426 : ℝ) / 65536) ((31226909130 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_046_1 <;> assumption
