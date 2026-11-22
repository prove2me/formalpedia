-- Prove2me | solution 1 for RH1E6S12.part_038_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T09:17:59.256169+00:00
-- url     : https://prove2.me/submissions/c8c35d51-1c0c-41d8-8e29-ad2119369954

import Definitions.Def_RH1E6S12_D038_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0310 : RS5.BandZeros ((47268432729 : ℝ) / 65536) ((47272938554 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0310.s0 RH1E6S12_0310.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0310.s0 RH1E6S12_0310.rest = RH1E6S12_0310.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0310.s0 :: RH1E6S12_0310.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0310.s0.t = ((47268432729 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0310.s0]
  have e1 : RH1E6S12_0310.sL.t = ((47272938554 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0310.sL]
  rw [e0, e1] at h
  exact h

theorem band_0311 : RS5.BandZeros ((47272938554 : ℝ) / 65536) ((47277412131 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0311.s0 RH1E6S12_0311.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0311.s0 RH1E6S12_0311.rest = RH1E6S12_0311.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0311.s0 :: RH1E6S12_0311.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0311.s0.t = ((47272938554 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0311.s0]
  have e1 : RH1E6S12_0311.sL.t = ((47277412131 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0311.sL]
  rw [e0, e1] at h
  exact h

theorem part_038_3 : RS5.BandZeros ((47268432729 : ℝ) / 65536) ((47277412131 : ℝ) / 65536) 254 := by
  have g0 := band_0310
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0311
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47268432729 : ℝ) / 65536) ((47277412131 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_038_3 <;> assumption
