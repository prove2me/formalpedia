-- Prove2me | solution 1 for RH1E6S14.part_038_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:43:50.554565+00:00
-- url     : https://prove2.me/submissions/adad8c52-e759-435c-8201-cc2c84977fbf

import Definitions.Def_RH1E6S14_D038_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0304 : RS5.BandZeros ((53779825043 : ℝ) / 65536) ((53784239036 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0304.s0 RH1E6S14_0304.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0304.s0 RH1E6S14_0304.rest = RH1E6S14_0304.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0304.s0 :: RH1E6S14_0304.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0304.s0.t = ((53779825043 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0304.s0]
  have e1 : RH1E6S14_0304.sL.t = ((53784239036 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0304.sL]
  rw [e0, e1] at h
  exact h

theorem band_0305 : RS5.BandZeros ((53784239036 : ℝ) / 65536) ((53788695831 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0305.s0 RH1E6S14_0305.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0305.s0 RH1E6S14_0305.rest = RH1E6S14_0305.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0305.s0 :: RH1E6S14_0305.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0305.s0.t = ((53784239036 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0305.s0]
  have e1 : RH1E6S14_0305.sL.t = ((53788695831 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0305.sL]
  rw [e0, e1] at h
  exact h

theorem part_038_0 : RS5.BandZeros ((53779825043 : ℝ) / 65536) ((53788695831 : ℝ) / 65536) 254 := by
  have g0 := band_0304
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0305
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53779825043 : ℝ) / 65536) ((53788695831 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_038_0 <;> assumption
