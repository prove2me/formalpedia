-- Prove2me | solution 1 for RH1E6S11.part_078_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:47:12.9578+00:00
-- url     : https://prove2.me/submissions/c085612c-0413-4aa9-8d58-171c74b629e9

import Definitions.Def_RH1E6S11_D078_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0630 : RS5.BandZeros ((45443608824 : ℝ) / 65536) ((45448103697 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0630.s0 RH1E6S11_0630.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0630.s0 RH1E6S11_0630.rest = RH1E6S11_0630.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0630.s0 :: RH1E6S11_0630.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0630.s0.t = ((45443608824 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0630.s0]
  have e1 : RH1E6S11_0630.sL.t = ((45448103697 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0630.sL]
  rw [e0, e1] at h
  exact h

theorem band_0631 : RS5.BandZeros ((45448103697 : ℝ) / 65536) ((45452616262 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0631.s0 RH1E6S11_0631.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0631.s0 RH1E6S11_0631.rest = RH1E6S11_0631.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0631.s0 :: RH1E6S11_0631.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0631.s0.t = ((45448103697 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0631.s0]
  have e1 : RH1E6S11_0631.sL.t = ((45452616262 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0631.sL]
  rw [e0, e1] at h
  exact h

theorem part_078_3 : RS5.BandZeros ((45443608824 : ℝ) / 65536) ((45452616262 : ℝ) / 65536) 254 := by
  have g0 := band_0630
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0631
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45443608824 : ℝ) / 65536) ((45452616262 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_078_3 <;> assumption
