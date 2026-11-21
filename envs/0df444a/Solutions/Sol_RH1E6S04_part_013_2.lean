-- Prove2me | solution 1 for RH1E6S04.part_013_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T08:53:15.566073+00:00
-- url     : https://prove2.me/submissions/76065ce3-0dc4-4ceb-91ba-b5739453d083

import Definitions.Def_RH1E6S04_D013_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0108 : RS5.BandZeros ((20184379723 : ℝ) / 65536) ((20189221862 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0108.s0 RH1E6S04_0108.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0108.s0 RH1E6S04_0108.rest = RH1E6S04_0108.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0108.s0 :: RH1E6S04_0108.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0108.s0.t = ((20184379723 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0108.s0]
  have e1 : RH1E6S04_0108.sL.t = ((20189221862 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0108.sL]
  rw [e0, e1] at h
  exact h

theorem band_0109 : RS5.BandZeros ((20189221862 : ℝ) / 65536) ((20194082956 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0109.s0 RH1E6S04_0109.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0109.s0 RH1E6S04_0109.rest = RH1E6S04_0109.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0109.s0 :: RH1E6S04_0109.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0109.s0.t = ((20189221862 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0109.s0]
  have e1 : RH1E6S04_0109.sL.t = ((20194082956 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0109.sL]
  rw [e0, e1] at h
  exact h

theorem part_013_2 : RS5.BandZeros ((20184379723 : ℝ) / 65536) ((20194082956 : ℝ) / 65536) 254 := by
  have g0 := band_0108
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0109
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20184379723 : ℝ) / 65536) ((20194082956 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_013_2 <;> assumption
