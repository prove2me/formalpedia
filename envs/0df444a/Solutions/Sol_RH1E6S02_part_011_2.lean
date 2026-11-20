-- Prove2me | solution 1 for RH1E6S02.part_011_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:32:09.271077+00:00
-- url     : https://prove2.me/submissions/d4ba8b43-a8ba-4c52-8550-9d48c2e1b224

import Definitions.Def_RH1E6S02_D011_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0092 : RS5.BandZeros ((13570456764 : ℝ) / 65536) ((13575486564 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0092.s0 RH1E6S02_0092.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0092.s0 RH1E6S02_0092.rest = RH1E6S02_0092.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0092.s0 :: RH1E6S02_0092.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0092.s0.t = ((13570456764 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0092.s0]
  have e1 : RH1E6S02_0092.sL.t = ((13575486564 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0092.sL]
  rw [e0, e1] at h
  exact h

theorem band_0093 : RS5.BandZeros ((13575486564 : ℝ) / 65536) ((13580513284 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0093.s0 RH1E6S02_0093.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0093.s0 RH1E6S02_0093.rest = RH1E6S02_0093.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0093.s0 :: RH1E6S02_0093.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0093.s0.t = ((13575486564 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0093.s0]
  have e1 : RH1E6S02_0093.sL.t = ((13580513284 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0093.sL]
  rw [e0, e1] at h
  exact h

theorem part_011_2 : RS5.BandZeros ((13570456764 : ℝ) / 65536) ((13580513284 : ℝ) / 65536) 254 := by
  have g0 := band_0092
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0093
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((13570456764 : ℝ) / 65536) ((13580513284 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_011_2 <;> assumption
