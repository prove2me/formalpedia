-- Prove2me | solution 1 for RH1E6S09.part_049_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:28:48.968253+00:00
-- url     : https://prove2.me/submissions/2d86c99e-07bc-4d6e-9d09-3dd6577941bc

import Definitions.Def_RH1E6S09_D049_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0398 : RS5.BandZeros ((37869768392 : ℝ) / 65536) ((37874360963 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0398.s0 RH1E6S09_0398.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0398.s0 RH1E6S09_0398.rest = RH1E6S09_0398.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0398.s0 :: RH1E6S09_0398.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0398.s0.t = ((37869768392 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0398.s0]
  have e1 : RH1E6S09_0398.sL.t = ((37874360963 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0398.sL]
  rw [e0, e1] at h
  exact h

theorem band_0399 : RS5.BandZeros ((37874360963 : ℝ) / 65536) ((37878943381 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0399.s0 RH1E6S09_0399.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0399.s0 RH1E6S09_0399.rest = RH1E6S09_0399.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0399.s0 :: RH1E6S09_0399.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0399.s0.t = ((37874360963 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0399.s0]
  have e1 : RH1E6S09_0399.sL.t = ((37878943381 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0399.sL]
  rw [e0, e1] at h
  exact h

theorem part_049_3 : RS5.BandZeros ((37869768392 : ℝ) / 65536) ((37878943381 : ℝ) / 65536) 254 := by
  have g0 := band_0398
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0399
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37869768392 : ℝ) / 65536) ((37878943381 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_049_3 <;> assumption
