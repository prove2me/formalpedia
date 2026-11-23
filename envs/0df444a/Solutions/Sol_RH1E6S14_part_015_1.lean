-- Prove2me | solution 1 for RH1E6S14.part_015_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T03:20:42.827449+00:00
-- url     : https://prove2.me/submissions/b415ba4e-6df7-4ab3-9574-ac039ba25850

import Definitions.Def_RH1E6S14_D015_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0122 : RS5.BandZeros ((52971334477 : ℝ) / 65536) ((52975766623 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0122.s0 RH1E6S14_0122.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0122.s0 RH1E6S14_0122.rest = RH1E6S14_0122.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0122.s0 :: RH1E6S14_0122.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0122.s0.t = ((52971334477 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0122.s0]
  have e1 : RH1E6S14_0122.sL.t = ((52975766623 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0122.sL]
  rw [e0, e1] at h
  exact h

theorem band_0123 : RS5.BandZeros ((52975766623 : ℝ) / 65536) ((52980213482 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0123.s0 RH1E6S14_0123.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0123.s0 RH1E6S14_0123.rest = RH1E6S14_0123.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0123.s0 :: RH1E6S14_0123.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0123.s0.t = ((52975766623 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0123.s0]
  have e1 : RH1E6S14_0123.sL.t = ((52980213482 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0123.sL]
  rw [e0, e1] at h
  exact h

theorem part_015_1 : RS5.BandZeros ((52971334477 : ℝ) / 65536) ((52980213482 : ℝ) / 65536) 254 := by
  have g0 := band_0122
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0123
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((52971334477 : ℝ) / 65536) ((52980213482 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_015_1 <;> assumption
