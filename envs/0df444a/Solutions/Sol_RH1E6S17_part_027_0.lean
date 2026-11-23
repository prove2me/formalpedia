-- Prove2me | solution 1 for RH1E6S17.part_027_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T21:02:43.173801+00:00
-- url     : https://prove2.me/submissions/a6885739-1a75-4346-af48-7d510516359c

import Definitions.Def_RH1E6S17_D027_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0216 : RS5.BandZeros ((63205752361 : ℝ) / 65536) ((63210114432 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0216.s0 RH1E6S17_0216.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0216.s0 RH1E6S17_0216.rest = RH1E6S17_0216.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0216.s0 :: RH1E6S17_0216.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0216.s0.t = ((63205752361 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0216.s0]
  have e1 : RH1E6S17_0216.sL.t = ((63210114432 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0216.sL]
  rw [e0, e1] at h
  exact h

theorem band_0217 : RS5.BandZeros ((63210114432 : ℝ) / 65536) ((63214485099 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0217.s0 RH1E6S17_0217.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0217.s0 RH1E6S17_0217.rest = RH1E6S17_0217.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0217.s0 :: RH1E6S17_0217.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0217.s0.t = ((63210114432 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0217.s0]
  have e1 : RH1E6S17_0217.sL.t = ((63214485099 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0217.sL]
  rw [e0, e1] at h
  exact h

theorem part_027_0 : RS5.BandZeros ((63205752361 : ℝ) / 65536) ((63214485099 : ℝ) / 65536) 254 := by
  have g0 := band_0216
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0217
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63205752361 : ℝ) / 65536) ((63214485099 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_027_0 <;> assumption
