-- Prove2me | solution 1 for RH1E6S16.part_080_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:50:13.716655+00:00
-- url     : https://prove2.me/submissions/26f3507f-0611-49bd-8025-6db6a7d05971

import Definitions.Def_RH1E6S16_D080_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0642 : RS5.BandZeros ((61804690263 : ℝ) / 65536) ((61809100915 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0642.s0 RH1E6S16_0642.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0642.s0 RH1E6S16_0642.rest = RH1E6S16_0642.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0642.s0 :: RH1E6S16_0642.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0642.s0.t = ((61804690263 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0642.s0]
  have e1 : RH1E6S16_0642.sL.t = ((61809100915 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0642.sL]
  rw [e0, e1] at h
  exact h

theorem band_0643 : RS5.BandZeros ((61809100915 : ℝ) / 65536) ((61813462527 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0643.s0 RH1E6S16_0643.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0643.s0 RH1E6S16_0643.rest = RH1E6S16_0643.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0643.s0 :: RH1E6S16_0643.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0643.s0.t = ((61809100915 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0643.s0]
  have e1 : RH1E6S16_0643.sL.t = ((61813462527 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0643.sL]
  rw [e0, e1] at h
  exact h

theorem part_080_1 : RS5.BandZeros ((61804690263 : ℝ) / 65536) ((61813462527 : ℝ) / 65536) 254 := by
  have g0 := band_0642
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0643
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61804690263 : ℝ) / 65536) ((61813462527 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_080_1 <;> assumption
