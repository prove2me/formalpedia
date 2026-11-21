-- Prove2me | solution 1 for RH1E6S04.part_029_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:30:25.641186+00:00
-- url     : https://prove2.me/submissions/64e93192-7503-4420-bdd4-39d29bb71f72

import Definitions.Def_RH1E6S04_D029_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0236 : RS5.BandZeros ((20803329580 : ℝ) / 65536) ((20808158216 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0236.s0 RH1E6S04_0236.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0236.s0 RH1E6S04_0236.rest = RH1E6S04_0236.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0236.s0 :: RH1E6S04_0236.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0236.s0.t = ((20803329580 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0236.s0]
  have e1 : RH1E6S04_0236.sL.t = ((20808158216 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0236.sL]
  rw [e0, e1] at h
  exact h

theorem band_0237 : RS5.BandZeros ((20808158216 : ℝ) / 65536) ((20812986749 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0237.s0 RH1E6S04_0237.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0237.s0 RH1E6S04_0237.rest = RH1E6S04_0237.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0237.s0 :: RH1E6S04_0237.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0237.s0.t = ((20808158216 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0237.s0]
  have e1 : RH1E6S04_0237.sL.t = ((20812986749 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0237.sL]
  rw [e0, e1] at h
  exact h

theorem part_029_2 : RS5.BandZeros ((20803329580 : ℝ) / 65536) ((20812986749 : ℝ) / 65536) 254 := by
  have g0 := band_0236
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0237
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20803329580 : ℝ) / 65536) ((20812986749 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_029_2 <;> assumption
