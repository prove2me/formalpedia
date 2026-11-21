-- Prove2me | solution 1 for RH1E6S05.part_006_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:20:49.906286+00:00
-- url     : https://prove2.me/submissions/2d5dff75-6f2e-41d1-a79e-31defed0b6fa

import Definitions.Def_RH1E6S05_D006_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0048 : RS5.BandZeros ((23167183331 : ℝ) / 65536) ((23171964462 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0048.s0 RH1E6S05_0048.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0048.s0 RH1E6S05_0048.rest = RH1E6S05_0048.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0048.s0 :: RH1E6S05_0048.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0048.s0.t = ((23167183331 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0048.s0]
  have e1 : RH1E6S05_0048.sL.t = ((23171964462 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0048.sL]
  rw [e0, e1] at h
  exact h

theorem band_0049 : RS5.BandZeros ((23171964462 : ℝ) / 65536) ((23176764325 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0049.s0 RH1E6S05_0049.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0049.s0 RH1E6S05_0049.rest = RH1E6S05_0049.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0049.s0 :: RH1E6S05_0049.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0049.s0.t = ((23171964462 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0049.s0]
  have e1 : RH1E6S05_0049.sL.t = ((23176764325 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0049.sL]
  rw [e0, e1] at h
  exact h

theorem part_006_0 : RS5.BandZeros ((23167183331 : ℝ) / 65536) ((23176764325 : ℝ) / 65536) 254 := by
  have g0 := band_0048
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0049
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((23167183331 : ℝ) / 65536) ((23176764325 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_006_0 <;> assumption
