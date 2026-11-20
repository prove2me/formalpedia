-- Prove2me | solution 1 for RH1E6S01.part_049_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:04:37.684851+00:00
-- url     : https://prove2.me/submissions/f9e99a46-e0d3-4cd3-afe8-81e7aa4e3fbe

import Definitions.Def_RH1E6S01_D049_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0396 : RS5.BandZeros ((11865168923 : ℝ) / 65536) ((11870261546 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0396.s0 RH1E6S01_0396.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0396.s0 RH1E6S01_0396.rest = RH1E6S01_0396.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0396.s0 :: RH1E6S01_0396.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0396.s0.t = ((11865168923 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0396.s0]
  have e1 : RH1E6S01_0396.sL.t = ((11870261546 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0396.sL]
  rw [e0, e1] at h
  exact h

theorem band_0397 : RS5.BandZeros ((11870261546 : ℝ) / 65536) ((11875353955 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0397.s0 RH1E6S01_0397.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0397.s0 RH1E6S01_0397.rest = RH1E6S01_0397.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0397.s0 :: RH1E6S01_0397.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0397.s0.t = ((11870261546 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0397.s0]
  have e1 : RH1E6S01_0397.sL.t = ((11875353955 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0397.sL]
  rw [e0, e1] at h
  exact h

theorem part_049_2 : RS5.BandZeros ((11865168923 : ℝ) / 65536) ((11875353955 : ℝ) / 65536) 254 := by
  have g0 := band_0396
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0397
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11865168923 : ℝ) / 65536) ((11875353955 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_049_2 <;> assumption
