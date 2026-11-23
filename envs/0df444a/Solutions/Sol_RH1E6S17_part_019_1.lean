-- Prove2me | solution 1 for RH1E6S17.part_019_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T20:37:03.234681+00:00
-- url     : https://prove2.me/submissions/ba712847-2998-40a1-b6d5-e713f3c0f270

import Definitions.Def_RH1E6S17_D019_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0154 : RS5.BandZeros ((62934168016 : ℝ) / 65536) ((62938540284 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0154.s0 RH1E6S17_0154.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0154.s0 RH1E6S17_0154.rest = RH1E6S17_0154.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0154.s0 :: RH1E6S17_0154.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0154.s0.t = ((62934168016 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0154.s0]
  have e1 : RH1E6S17_0154.sL.t = ((62938540284 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0154.sL]
  rw [e0, e1] at h
  exact h

theorem band_0155 : RS5.BandZeros ((62938540284 : ℝ) / 65536) ((62942929775 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0155.s0 RH1E6S17_0155.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0155.s0 RH1E6S17_0155.rest = RH1E6S17_0155.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0155.s0 :: RH1E6S17_0155.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0155.s0.t = ((62938540284 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0155.s0]
  have e1 : RH1E6S17_0155.sL.t = ((62942929775 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0155.sL]
  rw [e0, e1] at h
  exact h

theorem part_019_1 : RS5.BandZeros ((62934168016 : ℝ) / 65536) ((62942929775 : ℝ) / 65536) 254 := by
  have g0 := band_0154
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0155
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((62934168016 : ℝ) / 65536) ((62942929775 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_019_1 <;> assumption
