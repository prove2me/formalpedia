-- Prove2me | solution 1 for RH1E6S16.part_088_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:18:43.397909+00:00
-- url     : https://prove2.me/submissions/210045fd-0e8b-4e59-b1ae-cdfef04cc08b

import Definitions.Def_RH1E6S16_D088_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0710 : RS5.BandZeros ((62102989978 : ℝ) / 65536) ((62107384388 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0710.s0 RH1E6S16_0710.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0710.s0 RH1E6S16_0710.rest = RH1E6S16_0710.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0710.s0 :: RH1E6S16_0710.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0710.s0.t = ((62102989978 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0710.s0]
  have e1 : RH1E6S16_0710.sL.t = ((62107384388 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0710.sL]
  rw [e0, e1] at h
  exact h

theorem band_0711 : RS5.BandZeros ((62107384388 : ℝ) / 65536) ((62111752872 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0711.s0 RH1E6S16_0711.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0711.s0 RH1E6S16_0711.rest = RH1E6S16_0711.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0711.s0 :: RH1E6S16_0711.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0711.s0.t = ((62107384388 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0711.s0]
  have e1 : RH1E6S16_0711.sL.t = ((62111752872 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0711.sL]
  rw [e0, e1] at h
  exact h

theorem part_088_3 : RS5.BandZeros ((62102989978 : ℝ) / 65536) ((62111752872 : ℝ) / 65536) 254 := by
  have g0 := band_0710
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0711
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((62102989978 : ℝ) / 65536) ((62111752872 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_088_3 <;> assumption
