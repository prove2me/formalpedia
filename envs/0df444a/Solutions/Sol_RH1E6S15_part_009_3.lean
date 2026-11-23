-- Prove2me | solution 1 for RH1E6S15.part_009_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T08:22:13.089559+00:00
-- url     : https://prove2.me/submissions/01ee8945-4f55-4d16-9324-436d1f1ee918

import Definitions.Def_RH1E6S15_D009_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0078 : RS5.BandZeros ((56050716697 : ℝ) / 65536) ((56055123644 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0078.s0 RH1E6S15_0078.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0078.s0 RH1E6S15_0078.rest = RH1E6S15_0078.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0078.s0 :: RH1E6S15_0078.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0078.s0.t = ((56050716697 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0078.s0]
  have e1 : RH1E6S15_0078.sL.t = ((56055123644 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0078.sL]
  rw [e0, e1] at h
  exact h

theorem band_0079 : RS5.BandZeros ((56055123644 : ℝ) / 65536) ((56059553844 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0079.s0 RH1E6S15_0079.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0079.s0 RH1E6S15_0079.rest = RH1E6S15_0079.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0079.s0 :: RH1E6S15_0079.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0079.s0.t = ((56055123644 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0079.s0]
  have e1 : RH1E6S15_0079.sL.t = ((56059553844 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0079.sL]
  rw [e0, e1] at h
  exact h

theorem part_009_3 : RS5.BandZeros ((56050716697 : ℝ) / 65536) ((56059553844 : ℝ) / 65536) 254 := by
  have g0 := band_0078
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0079
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56050716697 : ℝ) / 65536) ((56059553844 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_009_3 <;> assumption
