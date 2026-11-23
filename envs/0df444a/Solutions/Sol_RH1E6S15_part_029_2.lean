-- Prove2me | solution 1 for RH1E6S15.part_029_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T09:38:47.073509+00:00
-- url     : https://prove2.me/submissions/9373e29a-5a92-4243-b69b-01b90c78abc2

import Definitions.Def_RH1E6S15_D029_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0236 : RS5.BandZeros ((56749313633 : ℝ) / 65536) ((56753737032 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0236.s0 RH1E6S15_0236.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0236.s0 RH1E6S15_0236.rest = RH1E6S15_0236.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0236.s0 :: RH1E6S15_0236.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0236.s0.t = ((56749313633 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0236.s0]
  have e1 : RH1E6S15_0236.sL.t = ((56753737032 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0236.sL]
  rw [e0, e1] at h
  exact h

theorem band_0237 : RS5.BandZeros ((56753737032 : ℝ) / 65536) ((56758147035 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0237.s0 RH1E6S15_0237.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0237.s0 RH1E6S15_0237.rest = RH1E6S15_0237.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0237.s0 :: RH1E6S15_0237.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0237.s0.t = ((56753737032 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0237.s0]
  have e1 : RH1E6S15_0237.sL.t = ((56758147035 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0237.sL]
  rw [e0, e1] at h
  exact h

theorem part_029_2 : RS5.BandZeros ((56749313633 : ℝ) / 65536) ((56758147035 : ℝ) / 65536) 254 := by
  have g0 := band_0236
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0237
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56749313633 : ℝ) / 65536) ((56758147035 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_029_2 <;> assumption
