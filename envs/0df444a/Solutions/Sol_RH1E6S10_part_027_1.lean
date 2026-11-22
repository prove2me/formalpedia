-- Prove2me | solution 1 for RH1E6S10.part_027_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T22:31:53.318508+00:00
-- url     : https://prove2.me/submissions/81e98d8b-a917-41ad-b574-2abc247d4b38

import Definitions.Def_RH1E6S10_D027_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0218 : RS5.BandZeros ((40314745346 : ℝ) / 65536) ((40319296014 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0218.s0 RH1E6S10_0218.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0218.s0 RH1E6S10_0218.rest = RH1E6S10_0218.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0218.s0 :: RH1E6S10_0218.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0218.s0.t = ((40314745346 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0218.s0]
  have e1 : RH1E6S10_0218.sL.t = ((40319296014 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0218.sL]
  rw [e0, e1] at h
  exact h

theorem band_0219 : RS5.BandZeros ((40319296014 : ℝ) / 65536) ((40323837680 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0219.s0 RH1E6S10_0219.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0219.s0 RH1E6S10_0219.rest = RH1E6S10_0219.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0219.s0 :: RH1E6S10_0219.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0219.s0.t = ((40319296014 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0219.s0]
  have e1 : RH1E6S10_0219.sL.t = ((40323837680 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0219.sL]
  rw [e0, e1] at h
  exact h

theorem part_027_1 : RS5.BandZeros ((40314745346 : ℝ) / 65536) ((40323837680 : ℝ) / 65536) 254 := by
  have g0 := band_0218
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0219
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40314745346 : ℝ) / 65536) ((40323837680 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_027_1 <;> assumption
