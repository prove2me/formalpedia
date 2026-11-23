-- Prove2me | solution 1 for RH1E6S16.part_068_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:12:19.5875+00:00
-- url     : https://prove2.me/submissions/c0975a38-dfb5-4cf9-8b84-29fecc69fa8f

import Definitions.Def_RH1E6S16_D068_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0550 : RS5.BandZeros ((61400941455 : ℝ) / 65536) ((61405316731 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0550.s0 RH1E6S16_0550.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0550.s0 RH1E6S16_0550.rest = RH1E6S16_0550.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0550.s0 :: RH1E6S16_0550.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0550.s0.t = ((61400941455 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0550.s0]
  have e1 : RH1E6S16_0550.sL.t = ((61405316731 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0550.sL]
  rw [e0, e1] at h
  exact h

theorem band_0551 : RS5.BandZeros ((61405316731 : ℝ) / 65536) ((61409703098 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0551.s0 RH1E6S16_0551.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0551.s0 RH1E6S16_0551.rest = RH1E6S16_0551.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0551.s0 :: RH1E6S16_0551.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0551.s0.t = ((61405316731 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0551.s0]
  have e1 : RH1E6S16_0551.sL.t = ((61409703098 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0551.sL]
  rw [e0, e1] at h
  exact h

theorem part_068_3 : RS5.BandZeros ((61400941455 : ℝ) / 65536) ((61409703098 : ℝ) / 65536) 254 := by
  have g0 := band_0550
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0551
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61400941455 : ℝ) / 65536) ((61409703098 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_068_3 <;> assumption
