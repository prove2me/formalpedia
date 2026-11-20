-- Prove2me | solution 1 for RH1E6S01.part_000_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:23:00.355856+00:00
-- url     : https://prove2.me/submissions/991e4a3c-9544-4525-a2dd-e939d9fda92b

import Definitions.Def_RH1E6S01_D000_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0004 : RS5.BandZeros ((9851137009 : ℝ) / 65536) ((9856318457 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0004.s0 RH1E6S01_0004.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0004.s0 RH1E6S01_0004.rest = RH1E6S01_0004.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0004.s0 :: RH1E6S01_0004.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0004.s0.t = ((9851137009 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0004.s0]
  have e1 : RH1E6S01_0004.sL.t = ((9856318457 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0004.sL]
  rw [e0, e1] at h
  exact h

theorem band_0005 : RS5.BandZeros ((9856318457 : ℝ) / 65536) ((9861525156 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0005.s0 RH1E6S01_0005.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0005.s0 RH1E6S01_0005.rest = RH1E6S01_0005.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0005.s0 :: RH1E6S01_0005.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0005.s0.t = ((9856318457 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0005.s0]
  have e1 : RH1E6S01_0005.sL.t = ((9861525156 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0005.sL]
  rw [e0, e1] at h
  exact h

theorem part_000_2 : RS5.BandZeros ((9851137009 : ℝ) / 65536) ((9861525156 : ℝ) / 65536) 254 := by
  have g0 := band_0004
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0005
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((9851137009 : ℝ) / 65536) ((9861525156 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_000_2 <;> assumption
