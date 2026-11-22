-- Prove2me | solution 1 for RH1E6S11.part_007_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:23:30.865267+00:00
-- url     : https://prove2.me/submissions/0527bf88-3108-4459-8f7b-fe3c6e6cbd05

import Definitions.Def_RH1E6S11_D007_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0060 : RS5.BandZeros ((42870051658 : ℝ) / 65536) ((42874595942 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0060.s0 RH1E6S11_0060.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0060.s0 RH1E6S11_0060.rest = RH1E6S11_0060.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0060.s0 :: RH1E6S11_0060.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0060.s0.t = ((42870051658 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0060.s0]
  have e1 : RH1E6S11_0060.sL.t = ((42874595942 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0060.sL]
  rw [e0, e1] at h
  exact h

theorem band_0061 : RS5.BandZeros ((42874595942 : ℝ) / 65536) ((42879122363 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0061.s0 RH1E6S11_0061.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0061.s0 RH1E6S11_0061.rest = RH1E6S11_0061.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0061.s0 :: RH1E6S11_0061.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0061.s0.t = ((42874595942 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0061.s0]
  have e1 : RH1E6S11_0061.sL.t = ((42879122363 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0061.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_2 : RS5.BandZeros ((42870051658 : ℝ) / 65536) ((42879122363 : ℝ) / 65536) 254 := by
  have g0 := band_0060
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0061
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((42870051658 : ℝ) / 65536) ((42879122363 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_007_2 <;> assumption
