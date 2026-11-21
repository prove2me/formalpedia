-- Prove2me | solution 1 for RH1E6S07.part_043_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T00:59:07.869806+00:00
-- url     : https://prove2.me/submissions/a36941fa-db94-4698-beb3-f331191e7290

import Definitions.Def_RH1E6S07_D043_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0346 : RS5.BandZeros ((31105892077 : ℝ) / 65536) ((31110522466 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0346.s0 RH1E6S07_0346.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0346.s0 RH1E6S07_0346.rest = RH1E6S07_0346.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0346.s0 :: RH1E6S07_0346.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0346.s0.t = ((31105892077 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0346.s0]
  have e1 : RH1E6S07_0346.sL.t = ((31110522466 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0346.sL]
  rw [e0, e1] at h
  exact h

theorem band_0347 : RS5.BandZeros ((31110522466 : ℝ) / 65536) ((31115189834 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0347.s0 RH1E6S07_0347.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0347.s0 RH1E6S07_0347.rest = RH1E6S07_0347.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0347.s0 :: RH1E6S07_0347.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0347.s0.t = ((31110522466 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0347.s0]
  have e1 : RH1E6S07_0347.sL.t = ((31115189834 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0347.sL]
  rw [e0, e1] at h
  exact h

theorem part_043_1 : RS5.BandZeros ((31105892077 : ℝ) / 65536) ((31115189834 : ℝ) / 65536) 254 := by
  have g0 := band_0346
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0347
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31105892077 : ℝ) / 65536) ((31115189834 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_043_1 <;> assumption
