-- Prove2me | solution 1 for RH1E6S01.part_070_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:46:40.562613+00:00
-- url     : https://prove2.me/submissions/bfa9f344-2cbb-4de6-8b22-7822b3349704

import Definitions.Def_RH1E6S01_D070_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0564 : RS5.BandZeros ((12717852695 : ℝ) / 65536) ((12722881267 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0564.s0 RH1E6S01_0564.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0564.s0 RH1E6S01_0564.rest = RH1E6S01_0564.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0564.s0 :: RH1E6S01_0564.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0564.s0.t = ((12717852695 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0564.s0]
  have e1 : RH1E6S01_0564.sL.t = ((12722881267 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0564.sL]
  rw [e0, e1] at h
  exact h

theorem band_0565 : RS5.BandZeros ((12722881267 : ℝ) / 65536) ((12727959431 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0565.s0 RH1E6S01_0565.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0565.s0 RH1E6S01_0565.rest = RH1E6S01_0565.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0565.s0 :: RH1E6S01_0565.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0565.s0.t = ((12722881267 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0565.s0]
  have e1 : RH1E6S01_0565.sL.t = ((12727959431 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0565.sL]
  rw [e0, e1] at h
  exact h

theorem part_070_2 : RS5.BandZeros ((12717852695 : ℝ) / 65536) ((12727959431 : ℝ) / 65536) 254 := by
  have g0 := band_0564
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0565
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12717852695 : ℝ) / 65536) ((12727959431 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_070_2 <;> assumption
