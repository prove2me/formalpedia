-- Prove2me | solution 1 for RH1E6S01.part_060_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:25:15.170975+00:00
-- url     : https://prove2.me/submissions/fc82b694-91bc-47cf-973b-9119397a37c0

import Definitions.Def_RH1E6S01_D060_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0482 : RS5.BandZeros ((12302368651 : ℝ) / 65536) ((12307463374 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0482.s0 RH1E6S01_0482.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0482.s0 RH1E6S01_0482.rest = RH1E6S01_0482.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0482.s0 :: RH1E6S01_0482.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0482.s0.t = ((12302368651 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0482.s0]
  have e1 : RH1E6S01_0482.sL.t = ((12307463374 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0482.sL]
  rw [e0, e1] at h
  exact h

theorem band_0483 : RS5.BandZeros ((12307463374 : ℝ) / 65536) ((12312487969 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0483.s0 RH1E6S01_0483.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0483.s0 RH1E6S01_0483.rest = RH1E6S01_0483.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0483.s0 :: RH1E6S01_0483.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0483.s0.t = ((12307463374 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0483.s0]
  have e1 : RH1E6S01_0483.sL.t = ((12312487969 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0483.sL]
  rw [e0, e1] at h
  exact h

theorem part_060_1 : RS5.BandZeros ((12302368651 : ℝ) / 65536) ((12312487969 : ℝ) / 65536) 254 := by
  have g0 := band_0482
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0483
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12302368651 : ℝ) / 65536) ((12312487969 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_060_1 <;> assumption
