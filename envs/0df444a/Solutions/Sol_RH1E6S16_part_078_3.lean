-- Prove2me | solution 1 for RH1E6S16.part_078_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:43:54.668167+00:00
-- url     : https://prove2.me/submissions/1774f763-f0cc-4584-bdeb-8d7eff393635

import Definitions.Def_RH1E6S16_D078_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0630 : RS5.BandZeros ((61752057901 : ℝ) / 65536) ((61756430659 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0630.s0 RH1E6S16_0630.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0630.s0 RH1E6S16_0630.rest = RH1E6S16_0630.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0630.s0 :: RH1E6S16_0630.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0630.s0.t = ((61752057901 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0630.s0]
  have e1 : RH1E6S16_0630.sL.t = ((61756430659 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0630.sL]
  rw [e0, e1] at h
  exact h

theorem band_0631 : RS5.BandZeros ((61756430659 : ℝ) / 65536) ((61760810708 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0631.s0 RH1E6S16_0631.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0631.s0 RH1E6S16_0631.rest = RH1E6S16_0631.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0631.s0 :: RH1E6S16_0631.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0631.s0.t = ((61756430659 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0631.s0]
  have e1 : RH1E6S16_0631.sL.t = ((61760810708 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0631.sL]
  rw [e0, e1] at h
  exact h

theorem part_078_3 : RS5.BandZeros ((61752057901 : ℝ) / 65536) ((61760810708 : ℝ) / 65536) 254 := by
  have g0 := band_0630
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0631
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61752057901 : ℝ) / 65536) ((61760810708 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_078_3 <;> assumption
