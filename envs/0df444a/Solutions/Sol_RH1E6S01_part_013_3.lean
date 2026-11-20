-- Prove2me | solution 1 for RH1E6S01.part_013_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:49:13.301262+00:00
-- url     : https://prove2.me/submissions/b57477ed-5425-4acd-a112-926fe85c0fee

import Definitions.Def_RH1E6S01_D013_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0110 : RS5.BandZeros ((10399444899 : ℝ) / 65536) ((10404603746 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0110.s0 RH1E6S01_0110.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0110.s0 RH1E6S01_0110.rest = RH1E6S01_0110.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0110.s0 :: RH1E6S01_0110.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0110.s0.t = ((10399444899 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0110.s0]
  have e1 : RH1E6S01_0110.sL.t = ((10404603746 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0110.sL]
  rw [e0, e1] at h
  exact h

theorem band_0111 : RS5.BandZeros ((10404603746 : ℝ) / 65536) ((10409762340 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0111.s0 RH1E6S01_0111.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0111.s0 RH1E6S01_0111.rest = RH1E6S01_0111.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0111.s0 :: RH1E6S01_0111.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0111.s0.t = ((10404603746 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0111.s0]
  have e1 : RH1E6S01_0111.sL.t = ((10409762340 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0111.sL]
  rw [e0, e1] at h
  exact h

theorem part_013_3 : RS5.BandZeros ((10399444899 : ℝ) / 65536) ((10409762340 : ℝ) / 65536) 254 := by
  have g0 := band_0110
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0111
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10399444899 : ℝ) / 65536) ((10409762340 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_013_3 <;> assumption
