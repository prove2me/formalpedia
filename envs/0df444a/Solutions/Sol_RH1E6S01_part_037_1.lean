-- Prove2me | solution 1 for RH1E6S01.part_037_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:38:41.149297+00:00
-- url     : https://prove2.me/submissions/ae87d630-746d-47d0-afa3-865b3ca09e44

import Definitions.Def_RH1E6S01_D037_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0298 : RS5.BandZeros ((11365030230 : ℝ) / 65536) ((11370154362 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0298.s0 RH1E6S01_0298.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0298.s0 RH1E6S01_0298.rest = RH1E6S01_0298.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0298.s0 :: RH1E6S01_0298.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0298.s0.t = ((11365030230 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0298.s0]
  have e1 : RH1E6S01_0298.sL.t = ((11370154362 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0298.sL]
  rw [e0, e1] at h
  exact h

theorem band_0299 : RS5.BandZeros ((11370154362 : ℝ) / 65536) ((11375278267 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0299.s0 RH1E6S01_0299.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0299.s0 RH1E6S01_0299.rest = RH1E6S01_0299.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0299.s0 :: RH1E6S01_0299.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0299.s0.t = ((11370154362 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0299.s0]
  have e1 : RH1E6S01_0299.sL.t = ((11375278267 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0299.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_1 : RS5.BandZeros ((11365030230 : ℝ) / 65536) ((11375278267 : ℝ) / 65536) 254 := by
  have g0 := band_0298
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0299
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11365030230 : ℝ) / 65536) ((11375278267 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_037_1 <;> assumption
