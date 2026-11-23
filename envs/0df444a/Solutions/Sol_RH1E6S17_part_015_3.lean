-- Prove2me | solution 1 for RH1E6S17.part_015_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T20:24:28.439962+00:00
-- url     : https://prove2.me/submissions/3f5f0be3-be83-4cce-a4f4-b7a6e710bb96

import Definitions.Def_RH1E6S17_D015_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0126 : RS5.BandZeros ((62811501275 : ℝ) / 65536) ((62815874258 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0126.s0 RH1E6S17_0126.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0126.s0 RH1E6S17_0126.rest = RH1E6S17_0126.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0126.s0 :: RH1E6S17_0126.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0126.s0.t = ((62811501275 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0126.s0]
  have e1 : RH1E6S17_0126.sL.t = ((62815874258 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0126.sL]
  rw [e0, e1] at h
  exact h

theorem band_0127 : RS5.BandZeros ((62815874258 : ℝ) / 65536) ((62820264466 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0127.s0 RH1E6S17_0127.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0127.s0 RH1E6S17_0127.rest = RH1E6S17_0127.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0127.s0 :: RH1E6S17_0127.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0127.s0.t = ((62815874258 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0127.s0]
  have e1 : RH1E6S17_0127.sL.t = ((62820264466 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0127.sL]
  rw [e0, e1] at h
  exact h

theorem part_015_3 : RS5.BandZeros ((62811501275 : ℝ) / 65536) ((62820264466 : ℝ) / 65536) 254 := by
  have g0 := band_0126
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0127
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((62811501275 : ℝ) / 65536) ((62820264466 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_015_3 <;> assumption
