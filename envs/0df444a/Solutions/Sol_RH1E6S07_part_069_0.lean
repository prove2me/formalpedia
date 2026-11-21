-- Prove2me | solution 1 for RH1E6S07.part_069_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T02:10:16.885188+00:00
-- url     : https://prove2.me/submissions/63688e49-1d9b-46e1-be75-d77dc5ec69b5

import Definitions.Def_RH1E6S07_D069_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0552 : RS5.BandZeros ((32063675798 : ℝ) / 65536) ((32068322644 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0552.s0 RH1E6S07_0552.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0552.s0 RH1E6S07_0552.rest = RH1E6S07_0552.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0552.s0 :: RH1E6S07_0552.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0552.s0.t = ((32063675798 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0552.s0]
  have e1 : RH1E6S07_0552.sL.t = ((32068322644 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0552.sL]
  rw [e0, e1] at h
  exact h

theorem band_0553 : RS5.BandZeros ((32068322644 : ℝ) / 65536) ((32072953376 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0553.s0 RH1E6S07_0553.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0553.s0 RH1E6S07_0553.rest = RH1E6S07_0553.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0553.s0 :: RH1E6S07_0553.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0553.s0.t = ((32068322644 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0553.s0]
  have e1 : RH1E6S07_0553.sL.t = ((32072953376 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0553.sL]
  rw [e0, e1] at h
  exact h

theorem part_069_0 : RS5.BandZeros ((32063675798 : ℝ) / 65536) ((32072953376 : ℝ) / 65536) 254 := by
  have g0 := band_0552
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0553
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((32063675798 : ℝ) / 65536) ((32072953376 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_069_0 <;> assumption
