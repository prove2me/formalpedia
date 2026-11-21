-- Prove2me | solution 1 for RH1E6S07.part_073_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T02:21:44.431092+00:00
-- url     : https://prove2.me/submissions/0457bcf5-1ee6-41d3-9467-d06543992f5f

import Definitions.Def_RH1E6S07_D073_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0590 : RS5.BandZeros ((32240072246 : ℝ) / 65536) ((32244708149 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0590.s0 RH1E6S07_0590.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0590.s0 RH1E6S07_0590.rest = RH1E6S07_0590.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0590.s0 :: RH1E6S07_0590.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0590.s0.t = ((32240072246 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0590.s0]
  have e1 : RH1E6S07_0590.sL.t = ((32244708149 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0590.sL]
  rw [e0, e1] at h
  exact h

theorem band_0591 : RS5.BandZeros ((32244708149 : ℝ) / 65536) ((32249343224 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0591.s0 RH1E6S07_0591.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0591.s0 RH1E6S07_0591.rest = RH1E6S07_0591.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0591.s0 :: RH1E6S07_0591.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0591.s0.t = ((32244708149 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0591.s0]
  have e1 : RH1E6S07_0591.sL.t = ((32249343224 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0591.sL]
  rw [e0, e1] at h
  exact h

theorem part_073_3 : RS5.BandZeros ((32240072246 : ℝ) / 65536) ((32249343224 : ℝ) / 65536) 254 := by
  have g0 := band_0590
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0591
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((32240072246 : ℝ) / 65536) ((32249343224 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_073_3 <;> assumption
