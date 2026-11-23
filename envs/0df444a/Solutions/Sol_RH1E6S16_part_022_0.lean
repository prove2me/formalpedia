-- Prove2me | solution 1 for RH1E6S16.part_022_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:17:28.891127+00:00
-- url     : https://prove2.me/submissions/6349a1c6-279a-49a9-9fd7-d3a5e2815ffd

import Definitions.Def_RH1E6S16_D022_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0176 : RS5.BandZeros ((59757219751 : ℝ) / 65536) ((59761599390 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0176.s0 RH1E6S16_0176.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0176.s0 RH1E6S16_0176.rest = RH1E6S16_0176.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0176.s0 :: RH1E6S16_0176.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0176.s0.t = ((59757219751 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0176.s0]
  have e1 : RH1E6S16_0176.sL.t = ((59761599390 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0176.sL]
  rw [e0, e1] at h
  exact h

theorem band_0177 : RS5.BandZeros ((59761599390 : ℝ) / 65536) ((59766023649 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0177.s0 RH1E6S16_0177.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0177.s0 RH1E6S16_0177.rest = RH1E6S16_0177.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0177.s0 :: RH1E6S16_0177.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0177.s0.t = ((59761599390 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0177.s0]
  have e1 : RH1E6S16_0177.sL.t = ((59766023649 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0177.sL]
  rw [e0, e1] at h
  exact h

theorem part_022_0 : RS5.BandZeros ((59757219751 : ℝ) / 65536) ((59766023649 : ℝ) / 65536) 254 := by
  have g0 := band_0176
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0177
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59757219751 : ℝ) / 65536) ((59766023649 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_022_0 <;> assumption
