-- Prove2me | solution 1 for RH1E6S14.part_005_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:48:27.761801+00:00
-- url     : https://prove2.me/submissions/cb74a44c-5357-4a23-9685-5cbedff4667f

import Definitions.Def_RH1E6S14_D005_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0046 : RS5.BandZeros ((52633400407 : ℝ) / 65536) ((52637872545 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0046.s0 RH1E6S14_0046.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0046.s0 RH1E6S14_0046.rest = RH1E6S14_0046.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0046.s0 :: RH1E6S14_0046.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0046.s0.t = ((52633400407 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0046.s0]
  have e1 : RH1E6S14_0046.sL.t = ((52637872545 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0046.sL]
  rw [e0, e1] at h
  exact h

theorem band_0047 : RS5.BandZeros ((52637872545 : ℝ) / 65536) ((52642317588 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0047.s0 RH1E6S14_0047.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0047.s0 RH1E6S14_0047.rest = RH1E6S14_0047.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0047.s0 :: RH1E6S14_0047.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0047.s0.t = ((52637872545 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0047.s0]
  have e1 : RH1E6S14_0047.sL.t = ((52642317588 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0047.sL]
  rw [e0, e1] at h
  exact h

theorem part_005_3 : RS5.BandZeros ((52633400407 : ℝ) / 65536) ((52642317588 : ℝ) / 65536) 254 := by
  have g0 := band_0046
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0047
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((52633400407 : ℝ) / 65536) ((52642317588 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_005_3 <;> assumption
