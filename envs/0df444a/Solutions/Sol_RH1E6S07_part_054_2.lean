-- Prove2me | solution 1 for RH1E6S07.part_054_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:28:41.563366+00:00
-- url     : https://prove2.me/submissions/dd872e52-7c64-4916-aa08-b7d923661110

import Definitions.Def_RH1E6S07_D054_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0436 : RS5.BandZeros ((31524652844 : ℝ) / 65536) ((31529297344 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0436.s0 RH1E6S07_0436.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0436.s0 RH1E6S07_0436.rest = RH1E6S07_0436.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0436.s0 :: RH1E6S07_0436.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0436.s0.t = ((31524652844 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0436.s0]
  have e1 : RH1E6S07_0436.sL.t = ((31529297344 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0436.sL]
  rw [e0, e1] at h
  exact h

theorem band_0437 : RS5.BandZeros ((31529297344 : ℝ) / 65536) ((31533952627 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0437.s0 RH1E6S07_0437.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0437.s0 RH1E6S07_0437.rest = RH1E6S07_0437.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0437.s0 :: RH1E6S07_0437.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0437.s0.t = ((31529297344 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0437.s0]
  have e1 : RH1E6S07_0437.sL.t = ((31533952627 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0437.sL]
  rw [e0, e1] at h
  exact h

theorem part_054_2 : RS5.BandZeros ((31524652844 : ℝ) / 65536) ((31533952627 : ℝ) / 65536) 254 := by
  have g0 := band_0436
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0437
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31524652844 : ℝ) / 65536) ((31533952627 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_054_2 <;> assumption
