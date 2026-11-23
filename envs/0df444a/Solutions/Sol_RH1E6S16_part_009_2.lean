-- Prove2me | solution 1 for RH1E6S16.part_009_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T14:26:42.560581+00:00
-- url     : https://prove2.me/submissions/75072675-9950-4703-a0e9-865e11acce9d

import Definitions.Def_RH1E6S16_D009_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0076 : RS5.BandZeros ((59317083477 : ℝ) / 65536) ((59321486635 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0076.s0 RH1E6S16_0076.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0076.s0 RH1E6S16_0076.rest = RH1E6S16_0076.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0076.s0 :: RH1E6S16_0076.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0076.s0.t = ((59317083477 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0076.s0]
  have e1 : RH1E6S16_0076.sL.t = ((59321486635 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0076.sL]
  rw [e0, e1] at h
  exact h

theorem band_0077 : RS5.BandZeros ((59321486635 : ℝ) / 65536) ((59325896706 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0077.s0 RH1E6S16_0077.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0077.s0 RH1E6S16_0077.rest = RH1E6S16_0077.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0077.s0 :: RH1E6S16_0077.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0077.s0.t = ((59321486635 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0077.s0]
  have e1 : RH1E6S16_0077.sL.t = ((59325896706 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0077.sL]
  rw [e0, e1] at h
  exact h

theorem part_009_2 : RS5.BandZeros ((59317083477 : ℝ) / 65536) ((59325896706 : ℝ) / 65536) 254 := by
  have g0 := band_0076
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0077
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59317083477 : ℝ) / 65536) ((59325896706 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_009_2 <;> assumption
