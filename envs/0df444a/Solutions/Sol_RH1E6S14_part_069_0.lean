-- Prove2me | solution 1 for RH1E6S14.part_069_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T06:22:49.502735+00:00
-- url     : https://prove2.me/submissions/ac2b64f9-2b7d-4ef7-b940-00192bbd664d

import Definitions.Def_RH1E6S14_D069_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0552 : RS5.BandZeros ((54879834798 : ℝ) / 65536) ((54884253827 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0552.s0 RH1E6S14_0552.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0552.s0 RH1E6S14_0552.rest = RH1E6S14_0552.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0552.s0 :: RH1E6S14_0552.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0552.s0.t = ((54879834798 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0552.s0]
  have e1 : RH1E6S14_0552.sL.t = ((54884253827 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0552.sL]
  rw [e0, e1] at h
  exact h

theorem band_0553 : RS5.BandZeros ((54884253827 : ℝ) / 65536) ((54888698025 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0553.s0 RH1E6S14_0553.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0553.s0 RH1E6S14_0553.rest = RH1E6S14_0553.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0553.s0 :: RH1E6S14_0553.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0553.s0.t = ((54884253827 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0553.s0]
  have e1 : RH1E6S14_0553.sL.t = ((54888698025 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0553.sL]
  rw [e0, e1] at h
  exact h

theorem part_069_0 : RS5.BandZeros ((54879834798 : ℝ) / 65536) ((54888698025 : ℝ) / 65536) 254 := by
  have g0 := band_0552
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0553
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((54879834798 : ℝ) / 65536) ((54888698025 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_069_0 <;> assumption
