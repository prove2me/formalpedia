-- Prove2me | solution 1 for RH1E6S15.part_072_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T12:21:20.361639+00:00
-- url     : https://prove2.me/submissions/e00f8336-684c-4b94-b917-b5719041955f

import Definitions.Def_RH1E6S15_D072_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0582 : RS5.BandZeros ((58276630992 : ℝ) / 65536) ((58281045442 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0582.s0 RH1E6S15_0582.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0582.s0 RH1E6S15_0582.rest = RH1E6S15_0582.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0582.s0 :: RH1E6S15_0582.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0582.s0.t = ((58276630992 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0582.s0]
  have e1 : RH1E6S15_0582.sL.t = ((58281045442 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0582.sL]
  rw [e0, e1] at h
  exact h

theorem band_0583 : RS5.BandZeros ((58281045442 : ℝ) / 65536) ((58285452826 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0583.s0 RH1E6S15_0583.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0583.s0 RH1E6S15_0583.rest = RH1E6S15_0583.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0583.s0 :: RH1E6S15_0583.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0583.s0.t = ((58281045442 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0583.s0]
  have e1 : RH1E6S15_0583.sL.t = ((58285452826 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0583.sL]
  rw [e0, e1] at h
  exact h

theorem part_072_3 : RS5.BandZeros ((58276630992 : ℝ) / 65536) ((58285452826 : ℝ) / 65536) 254 := by
  have g0 := band_0582
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0583
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58276630992 : ℝ) / 65536) ((58285452826 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_072_3 <;> assumption
