-- Prove2me | solution 1 for RH1E6S07.part_058_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:42:27.164866+00:00
-- url     : https://prove2.me/submissions/182c7ac5-4ec1-41ef-94b1-876e419b55c9

import Definitions.Def_RH1E6S07_D058_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0466 : RS5.BandZeros ((31664128781 : ℝ) / 65536) ((31668780253 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0466.s0 RH1E6S07_0466.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0466.s0 RH1E6S07_0466.rest = RH1E6S07_0466.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0466.s0 :: RH1E6S07_0466.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0466.s0.t = ((31664128781 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0466.s0]
  have e1 : RH1E6S07_0466.sL.t = ((31668780253 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0466.sL]
  rw [e0, e1] at h
  exact h

theorem band_0467 : RS5.BandZeros ((31668780253 : ℝ) / 65536) ((31673432538 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0467.s0 RH1E6S07_0467.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0467.s0 RH1E6S07_0467.rest = RH1E6S07_0467.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0467.s0 :: RH1E6S07_0467.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0467.s0.t = ((31668780253 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0467.s0]
  have e1 : RH1E6S07_0467.sL.t = ((31673432538 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0467.sL]
  rw [e0, e1] at h
  exact h

theorem part_058_1 : RS5.BandZeros ((31664128781 : ℝ) / 65536) ((31673432538 : ℝ) / 65536) 254 := by
  have g0 := band_0466
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0467
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31664128781 : ℝ) / 65536) ((31673432538 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_058_1 <;> assumption
