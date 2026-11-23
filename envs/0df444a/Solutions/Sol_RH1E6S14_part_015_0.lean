-- Prove2me | solution 1 for RH1E6S14.part_015_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T03:20:40.801469+00:00
-- url     : https://prove2.me/submissions/213f24d0-8a10-46c0-84e0-16c8407a40ce

import Definitions.Def_RH1E6S14_D015_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0120 : RS5.BandZeros ((52962438208 : ℝ) / 65536) ((52966901894 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0120.s0 RH1E6S14_0120.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0120.s0 RH1E6S14_0120.rest = RH1E6S14_0120.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0120.s0 :: RH1E6S14_0120.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0120.s0.t = ((52962438208 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0120.s0]
  have e1 : RH1E6S14_0120.sL.t = ((52966901894 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0120.sL]
  rw [e0, e1] at h
  exact h

theorem band_0121 : RS5.BandZeros ((52966901894 : ℝ) / 65536) ((52971334477 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0121.s0 RH1E6S14_0121.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0121.s0 RH1E6S14_0121.rest = RH1E6S14_0121.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0121.s0 :: RH1E6S14_0121.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0121.s0.t = ((52966901894 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0121.s0]
  have e1 : RH1E6S14_0121.sL.t = ((52971334477 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0121.sL]
  rw [e0, e1] at h
  exact h

theorem part_015_0 : RS5.BandZeros ((52962438208 : ℝ) / 65536) ((52971334477 : ℝ) / 65536) 254 := by
  have g0 := band_0120
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0121
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((52962438208 : ℝ) / 65536) ((52971334477 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_015_0 <;> assumption
