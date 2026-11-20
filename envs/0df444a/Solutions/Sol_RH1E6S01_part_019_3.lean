-- Prove2me | solution 1 for RH1E6S01.part_019_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:01:01.347993+00:00
-- url     : https://prove2.me/submissions/7b560605-8d7f-4855-9ce6-2c2e325f067c

import Definitions.Def_RH1E6S01_D019_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0158 : RS5.BandZeros ((10646777556 : ℝ) / 65536) ((10651934603 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0158.s0 RH1E6S01_0158.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0158.s0 RH1E6S01_0158.rest = RH1E6S01_0158.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0158.s0 :: RH1E6S01_0158.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0158.s0.t = ((10646777556 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0158.s0]
  have e1 : RH1E6S01_0158.sL.t = ((10651934603 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0158.sL]
  rw [e0, e1] at h
  exact h

theorem band_0159 : RS5.BandZeros ((10651934603 : ℝ) / 65536) ((10657081273 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0159.s0 RH1E6S01_0159.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0159.s0 RH1E6S01_0159.rest = RH1E6S01_0159.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0159.s0 :: RH1E6S01_0159.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0159.s0.t = ((10651934603 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0159.s0]
  have e1 : RH1E6S01_0159.sL.t = ((10657081273 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0159.sL]
  rw [e0, e1] at h
  exact h

theorem part_019_3 : RS5.BandZeros ((10646777556 : ℝ) / 65536) ((10657081273 : ℝ) / 65536) 254 := by
  have g0 := band_0158
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0159
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10646777556 : ℝ) / 65536) ((10657081273 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_019_3 <;> assumption
