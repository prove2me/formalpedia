-- Prove2me | solution 1 for RH1E6S09.part_057_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:47:53.530663+00:00
-- url     : https://prove2.me/submissions/0beb996b-6e71-466c-b721-42365f450c87

import Definitions.Def_RH1E6S09_D057_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0456 : RS5.BandZeros ((38135083577 : ℝ) / 65536) ((38139663496 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0456.s0 RH1E6S09_0456.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0456.s0 RH1E6S09_0456.rest = RH1E6S09_0456.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0456.s0 :: RH1E6S09_0456.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0456.s0.t = ((38135083577 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0456.s0]
  have e1 : RH1E6S09_0456.sL.t = ((38139663496 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0456.sL]
  rw [e0, e1] at h
  exact h

theorem band_0457 : RS5.BandZeros ((38139663496 : ℝ) / 65536) ((38144217670 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0457.s0 RH1E6S09_0457.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0457.s0 RH1E6S09_0457.rest = RH1E6S09_0457.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0457.s0 :: RH1E6S09_0457.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0457.s0.t = ((38139663496 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0457.s0]
  have e1 : RH1E6S09_0457.sL.t = ((38144217670 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0457.sL]
  rw [e0, e1] at h
  exact h

theorem part_057_0 : RS5.BandZeros ((38135083577 : ℝ) / 65536) ((38144217670 : ℝ) / 65536) 254 := by
  have g0 := band_0456
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0457
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38135083577 : ℝ) / 65536) ((38144217670 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_057_0 <;> assumption
