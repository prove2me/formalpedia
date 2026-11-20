-- Prove2me | solution 1 for RH1E6S00.part_071_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:08:56.061772+00:00
-- url     : https://prove2.me/submissions/81df9797-8191-474a-9b73-d5df1b267797

import Definitions.Def_RH1E6S00_D071_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0568 : RS5.BandZeros ((9561342909 : ℝ) / 65536) ((9566565341 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0568.s0 RH1E6S00_0568.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0568.s0 RH1E6S00_0568.rest = RH1E6S00_0568.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0568.s0 :: RH1E6S00_0568.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0568.s0.t = ((9561342909 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0568.s0]
  have e1 : RH1E6S00_0568.sL.t = ((9566565341 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0568.sL]
  rw [e0, e1] at h
  exact h

theorem band_0569 : RS5.BandZeros ((9566565341 : ℝ) / 65536) ((9571767011 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0569.s0 RH1E6S00_0569.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0569.s0 RH1E6S00_0569.rest = RH1E6S00_0569.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0569.s0 :: RH1E6S00_0569.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0569.s0.t = ((9566565341 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0569.s0]
  have e1 : RH1E6S00_0569.sL.t = ((9571767011 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0569.sL]
  rw [e0, e1] at h
  exact h

theorem part_071_0 : RS5.BandZeros ((9561342909 : ℝ) / 65536) ((9571767011 : ℝ) / 65536) 254 := by
  have g0 := band_0568
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0569
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9561342909 : ℝ) / 65536) ((9571767011 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_071_0 <;> assumption
