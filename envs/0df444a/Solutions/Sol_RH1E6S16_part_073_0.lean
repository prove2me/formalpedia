-- Prove2me | solution 1 for RH1E6S16.part_073_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:28:05.304802+00:00
-- url     : https://prove2.me/submissions/897c54be-cf08-4da3-9f0e-ba8da999ac10

import Definitions.Def_RH1E6S16_D073_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0584 : RS5.BandZeros ((61550178224 : ℝ) / 65536) ((61554560242 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0584.s0 RH1E6S16_0584.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0584.s0 RH1E6S16_0584.rest = RH1E6S16_0584.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0584.s0 :: RH1E6S16_0584.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0584.s0.t = ((61550178224 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0584.s0]
  have e1 : RH1E6S16_0584.sL.t = ((61554560242 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0584.sL]
  rw [e0, e1] at h
  exact h

theorem band_0585 : RS5.BandZeros ((61554560242 : ℝ) / 65536) ((61558953809 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0585.s0 RH1E6S16_0585.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0585.s0 RH1E6S16_0585.rest = RH1E6S16_0585.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0585.s0 :: RH1E6S16_0585.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0585.s0.t = ((61554560242 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0585.s0]
  have e1 : RH1E6S16_0585.sL.t = ((61558953809 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0585.sL]
  rw [e0, e1] at h
  exact h

theorem part_073_0 : RS5.BandZeros ((61550178224 : ℝ) / 65536) ((61558953809 : ℝ) / 65536) 254 := by
  have g0 := band_0584
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0585
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61550178224 : ℝ) / 65536) ((61558953809 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_073_0 <;> assumption
