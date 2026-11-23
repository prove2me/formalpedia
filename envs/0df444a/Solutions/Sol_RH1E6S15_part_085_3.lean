-- Prove2me | solution 1 for RH1E6S15.part_085_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:20:55.383813+00:00
-- url     : https://prove2.me/submissions/791bb542-3e38-4b1b-96e1-1d6b911658ef

import Definitions.Def_RH1E6S15_D085_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0686 : RS5.BandZeros ((58735050673 : ℝ) / 65536) ((58739466969 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0686.s0 RH1E6S15_0686.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0686.s0 RH1E6S15_0686.rest = RH1E6S15_0686.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0686.s0 :: RH1E6S15_0686.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0686.s0.t = ((58735050673 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0686.s0]
  have e1 : RH1E6S15_0686.sL.t = ((58739466969 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0686.sL]
  rw [e0, e1] at h
  exact h

theorem band_0687 : RS5.BandZeros ((58739466969 : ℝ) / 65536) ((58743871006 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0687.s0 RH1E6S15_0687.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0687.s0 RH1E6S15_0687.rest = RH1E6S15_0687.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0687.s0 :: RH1E6S15_0687.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0687.s0.t = ((58739466969 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0687.s0]
  have e1 : RH1E6S15_0687.sL.t = ((58743871006 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0687.sL]
  rw [e0, e1] at h
  exact h

theorem part_085_3 : RS5.BandZeros ((58735050673 : ℝ) / 65536) ((58743871006 : ℝ) / 65536) 254 := by
  have g0 := band_0686
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0687
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58735050673 : ℝ) / 65536) ((58743871006 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_085_3 <;> assumption
