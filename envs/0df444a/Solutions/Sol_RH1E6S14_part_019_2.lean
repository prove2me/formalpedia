-- Prove2me | solution 1 for RH1E6S14.part_019_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T03:35:23.491804+00:00
-- url     : https://prove2.me/submissions/0e1c25ba-7413-4602-a785-05c810fd7be0

import Definitions.Def_RH1E6S14_D019_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0156 : RS5.BandZeros ((53122443973 : ℝ) / 65536) ((53126901612 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0156.s0 RH1E6S14_0156.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0156.s0 RH1E6S14_0156.rest = RH1E6S14_0156.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0156.s0 :: RH1E6S14_0156.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0156.s0.t = ((53122443973 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0156.s0]
  have e1 : RH1E6S14_0156.sL.t = ((53126901612 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0156.sL]
  rw [e0, e1] at h
  exact h

theorem band_0157 : RS5.BandZeros ((53126901612 : ℝ) / 65536) ((53131319324 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0157.s0 RH1E6S14_0157.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0157.s0 RH1E6S14_0157.rest = RH1E6S14_0157.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0157.s0 :: RH1E6S14_0157.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0157.s0.t = ((53126901612 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0157.s0]
  have e1 : RH1E6S14_0157.sL.t = ((53131319324 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0157.sL]
  rw [e0, e1] at h
  exact h

theorem part_019_2 : RS5.BandZeros ((53122443973 : ℝ) / 65536) ((53131319324 : ℝ) / 65536) 254 := by
  have g0 := band_0156
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0157
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53122443973 : ℝ) / 65536) ((53131319324 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_019_2 <;> assumption
