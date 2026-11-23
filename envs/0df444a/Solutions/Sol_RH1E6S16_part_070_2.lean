-- Prove2me | solution 1 for RH1E6S16.part_070_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:18:35.442261+00:00
-- url     : https://prove2.me/submissions/61369afe-3e5d-4a1b-9e1e-c04e1012bfe1

import Definitions.Def_RH1E6S16_D070_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0564 : RS5.BandZeros ((61462388469 : ℝ) / 65536) ((61466776209 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0564.s0 RH1E6S16_0564.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0564.s0 RH1E6S16_0564.rest = RH1E6S16_0564.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0564.s0 :: RH1E6S16_0564.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0564.s0.t = ((61462388469 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0564.s0]
  have e1 : RH1E6S16_0564.sL.t = ((61466776209 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0564.sL]
  rw [e0, e1] at h
  exact h

theorem band_0565 : RS5.BandZeros ((61466776209 : ℝ) / 65536) ((61471169014 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0565.s0 RH1E6S16_0565.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0565.s0 RH1E6S16_0565.rest = RH1E6S16_0565.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0565.s0 :: RH1E6S16_0565.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0565.s0.t = ((61466776209 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0565.s0]
  have e1 : RH1E6S16_0565.sL.t = ((61471169014 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0565.sL]
  rw [e0, e1] at h
  exact h

theorem part_070_2 : RS5.BandZeros ((61462388469 : ℝ) / 65536) ((61471169014 : ℝ) / 65536) 254 := by
  have g0 := band_0564
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0565
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61462388469 : ℝ) / 65536) ((61471169014 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_070_2 <;> assumption
