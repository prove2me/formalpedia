-- Prove2me | solution 1 for RH1E6S04.part_077_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T11:18:23.68725+00:00
-- url     : https://prove2.me/submissions/bd8f5e4a-16c9-4857-a40c-3d9f7155880a

import Definitions.Def_RH1E6S04_D077_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0622 : RS5.BandZeros ((22659772808 : ℝ) / 65536) ((22664563637 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0622.s0 RH1E6S04_0622.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0622.s0 RH1E6S04_0622.rest = RH1E6S04_0622.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0622.s0 :: RH1E6S04_0622.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0622.s0.t = ((22659772808 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0622.s0]
  have e1 : RH1E6S04_0622.sL.t = ((22664563637 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0622.sL]
  rw [e0, e1] at h
  exact h

theorem band_0623 : RS5.BandZeros ((22664563637 : ℝ) / 65536) ((22669344943 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0623.s0 RH1E6S04_0623.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0623.s0 RH1E6S04_0623.rest = RH1E6S04_0623.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0623.s0 :: RH1E6S04_0623.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0623.s0.t = ((22664563637 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0623.s0]
  have e1 : RH1E6S04_0623.sL.t = ((22669344943 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0623.sL]
  rw [e0, e1] at h
  exact h

theorem part_077_3 : RS5.BandZeros ((22659772808 : ℝ) / 65536) ((22669344943 : ℝ) / 65536) 254 := by
  have g0 := band_0622
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0623
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22659772808 : ℝ) / 65536) ((22669344943 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_077_3 <;> assumption
