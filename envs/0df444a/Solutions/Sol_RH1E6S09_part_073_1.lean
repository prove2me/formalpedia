-- Prove2me | solution 1 for RH1E6S09.part_073_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T14:43:20.481775+00:00
-- url     : https://prove2.me/submissions/5adb7de0-7240-489c-81e6-23a8005f9c3d

import Definitions.Def_RH1E6S09_D073_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0586 : RS5.BandZeros ((38729152672 : ℝ) / 65536) ((38733723550 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0586.s0 RH1E6S09_0586.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0586.s0 RH1E6S09_0586.rest = RH1E6S09_0586.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0586.s0 :: RH1E6S09_0586.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0586.s0.t = ((38729152672 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0586.s0]
  have e1 : RH1E6S09_0586.sL.t = ((38733723550 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0586.sL]
  rw [e0, e1] at h
  exact h

theorem band_0587 : RS5.BandZeros ((38733723550 : ℝ) / 65536) ((38738276860 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0587.s0 RH1E6S09_0587.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0587.s0 RH1E6S09_0587.rest = RH1E6S09_0587.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0587.s0 :: RH1E6S09_0587.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0587.s0.t = ((38733723550 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0587.s0]
  have e1 : RH1E6S09_0587.sL.t = ((38738276860 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0587.sL]
  rw [e0, e1] at h
  exact h

theorem part_073_1 : RS5.BandZeros ((38729152672 : ℝ) / 65536) ((38738276860 : ℝ) / 65536) 254 := by
  have g0 := band_0586
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0587
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38729152672 : ℝ) / 65536) ((38738276860 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_073_1 <;> assumption
