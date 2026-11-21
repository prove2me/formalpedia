-- Prove2me | solution 1 for RH1E6S07.part_024_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T00:03:35.00636+00:00
-- url     : https://prove2.me/submissions/e9b1c25a-d227-4ade-b189-8fb50e55c40a

import Definitions.Def_RH1E6S07_D024_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0198 : RS5.BandZeros ((30416139211 : ℝ) / 65536) ((30420803856 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0198.s0 RH1E6S07_0198.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0198.s0 RH1E6S07_0198.rest = RH1E6S07_0198.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0198.s0 :: RH1E6S07_0198.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0198.s0.t = ((30416139211 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0198.s0]
  have e1 : RH1E6S07_0198.sL.t = ((30420803856 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0198.sL]
  rw [e0, e1] at h
  exact h

theorem band_0199 : RS5.BandZeros ((30420803856 : ℝ) / 65536) ((30425471788 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0199.s0 RH1E6S07_0199.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0199.s0 RH1E6S07_0199.rest = RH1E6S07_0199.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0199.s0 :: RH1E6S07_0199.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0199.s0.t = ((30420803856 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0199.s0]
  have e1 : RH1E6S07_0199.sL.t = ((30425471788 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0199.sL]
  rw [e0, e1] at h
  exact h

theorem part_024_3 : RS5.BandZeros ((30416139211 : ℝ) / 65536) ((30425471788 : ℝ) / 65536) 254 := by
  have g0 := band_0198
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0199
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30416139211 : ℝ) / 65536) ((30425471788 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_024_3 <;> assumption
