-- Prove2me | solution 1 for RH1E6S10.part_053_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T01:22:39.071181+00:00
-- url     : https://prove2.me/submissions/0010fe22-efa2-47a4-b00b-64c25b39b507

import Definitions.Def_RH1E6S10_D053_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0430 : RS5.BandZeros ((41278488280 : ℝ) / 65536) ((41283038552 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0430.s0 RH1E6S10_0430.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0430.s0 RH1E6S10_0430.rest = RH1E6S10_0430.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0430.s0 :: RH1E6S10_0430.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0430.s0.t = ((41278488280 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0430.s0]
  have e1 : RH1E6S10_0430.sL.t = ((41283038552 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0430.sL]
  rw [e0, e1] at h
  exact h

theorem band_0431 : RS5.BandZeros ((41283038552 : ℝ) / 65536) ((41287579842 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0431.s0 RH1E6S10_0431.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0431.s0 RH1E6S10_0431.rest = RH1E6S10_0431.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0431.s0 :: RH1E6S10_0431.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0431.s0.t = ((41283038552 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0431.s0]
  have e1 : RH1E6S10_0431.sL.t = ((41287579842 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0431.sL]
  rw [e0, e1] at h
  exact h

theorem part_053_3 : RS5.BandZeros ((41278488280 : ℝ) / 65536) ((41287579842 : ℝ) / 65536) 254 := by
  have g0 := band_0430
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0431
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41278488280 : ℝ) / 65536) ((41287579842 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_053_3 <;> assumption
