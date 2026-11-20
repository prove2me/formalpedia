-- Prove2me | solution 1 for RH1E6S01.part_036_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:36:21.136182+00:00
-- url     : https://prove2.me/submissions/e868743a-cadf-4262-a30c-f10fc729732a

import Definitions.Def_RH1E6S01_D036_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0292 : RS5.BandZeros ((11334351180 : ℝ) / 65536) ((11339456527 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0292.s0 RH1E6S01_0292.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0292.s0 RH1E6S01_0292.rest = RH1E6S01_0292.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0292.s0 :: RH1E6S01_0292.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0292.s0.t = ((11334351180 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0292.s0]
  have e1 : RH1E6S01_0292.sL.t = ((11339456527 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0292.sL]
  rw [e0, e1] at h
  exact h

theorem band_0293 : RS5.BandZeros ((11339456527 : ℝ) / 65536) ((11344581788 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0293.s0 RH1E6S01_0293.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0293.s0 RH1E6S01_0293.rest = RH1E6S01_0293.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0293.s0 :: RH1E6S01_0293.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0293.s0.t = ((11339456527 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0293.s0]
  have e1 : RH1E6S01_0293.sL.t = ((11344581788 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0293.sL]
  rw [e0, e1] at h
  exact h

theorem part_036_2 : RS5.BandZeros ((11334351180 : ℝ) / 65536) ((11344581788 : ℝ) / 65536) 254 := by
  have g0 := band_0292
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0293
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11334351180 : ℝ) / 65536) ((11344581788 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_036_2 <;> assumption
