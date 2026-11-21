-- Prove2me | solution 1 for RH1E6S07.part_039_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T00:47:10.401669+00:00
-- url     : https://prove2.me/submissions/6f09fc1d-0627-4037-b6aa-f0c9a44008eb

import Definitions.Def_RH1E6S07_D039_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0314 : RS5.BandZeros ((30956869209 : ℝ) / 65536) ((30961534221 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0314.s0 RH1E6S07_0314.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0314.s0 RH1E6S07_0314.rest = RH1E6S07_0314.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0314.s0 :: RH1E6S07_0314.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0314.s0.t = ((30956869209 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0314.s0]
  have e1 : RH1E6S07_0314.sL.t = ((30961534221 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0314.sL]
  rw [e0, e1] at h
  exact h

theorem band_0315 : RS5.BandZeros ((30961534221 : ℝ) / 65536) ((30966166232 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0315.s0 RH1E6S07_0315.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0315.s0 RH1E6S07_0315.rest = RH1E6S07_0315.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0315.s0 :: RH1E6S07_0315.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0315.s0.t = ((30961534221 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0315.s0]
  have e1 : RH1E6S07_0315.sL.t = ((30966166232 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0315.sL]
  rw [e0, e1] at h
  exact h

theorem part_039_1 : RS5.BandZeros ((30956869209 : ℝ) / 65536) ((30966166232 : ℝ) / 65536) 254 := by
  have g0 := band_0314
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0315
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30956869209 : ℝ) / 65536) ((30966166232 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_039_1 <;> assumption
