-- Prove2me | solution 1 for RH1E6S16.part_020_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:11:27.984084+00:00
-- url     : https://prove2.me/submissions/461599d2-e358-49eb-93cf-7ce4353c4f0b

import Definitions.Def_RH1E6S16_D020_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0162 : RS5.BandZeros ((59695609582 : ℝ) / 65536) ((59700017405 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0162.s0 RH1E6S16_0162.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0162.s0 RH1E6S16_0162.rest = RH1E6S16_0162.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0162.s0 :: RH1E6S16_0162.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0162.s0.t = ((59695609582 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0162.s0]
  have e1 : RH1E6S16_0162.sL.t = ((59700017405 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0162.sL]
  rw [e0, e1] at h
  exact h

theorem band_0163 : RS5.BandZeros ((59700017405 : ℝ) / 65536) ((59704413104 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0163.s0 RH1E6S16_0163.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0163.s0 RH1E6S16_0163.rest = RH1E6S16_0163.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0163.s0 :: RH1E6S16_0163.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0163.s0.t = ((59700017405 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0163.s0]
  have e1 : RH1E6S16_0163.sL.t = ((59704413104 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0163.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_1 : RS5.BandZeros ((59695609582 : ℝ) / 65536) ((59704413104 : ℝ) / 65536) 254 := by
  have g0 := band_0162
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0163
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59695609582 : ℝ) / 65536) ((59704413104 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_020_1 <;> assumption
