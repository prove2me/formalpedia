-- Prove2me | solution 1 for RH1E6S16.part_078_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:43:52.559114+00:00
-- url     : https://prove2.me/submissions/f5271078-84f4-47eb-8551-9f121052008e

import Definitions.Def_RH1E6S16_D078_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0628 : RS5.BandZeros ((61743263883 : ℝ) / 65536) ((61747653171 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0628.s0 RH1E6S16_0628.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0628.s0 RH1E6S16_0628.rest = RH1E6S16_0628.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0628.s0 :: RH1E6S16_0628.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0628.s0.t = ((61743263883 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0628.s0]
  have e1 : RH1E6S16_0628.sL.t = ((61747653171 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0628.sL]
  rw [e0, e1] at h
  exact h

theorem band_0629 : RS5.BandZeros ((61747653171 : ℝ) / 65536) ((61752057901 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0629.s0 RH1E6S16_0629.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0629.s0 RH1E6S16_0629.rest = RH1E6S16_0629.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0629.s0 :: RH1E6S16_0629.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0629.s0.t = ((61747653171 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0629.s0]
  have e1 : RH1E6S16_0629.sL.t = ((61752057901 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0629.sL]
  rw [e0, e1] at h
  exact h

theorem part_078_2 : RS5.BandZeros ((61743263883 : ℝ) / 65536) ((61752057901 : ℝ) / 65536) 254 := by
  have g0 := band_0628
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0629
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61743263883 : ℝ) / 65536) ((61752057901 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_078_2 <;> assumption
