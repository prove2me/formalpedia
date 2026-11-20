-- Prove2me | solution 1 for RH1E6S01.part_067_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:41:48.083502+00:00
-- url     : https://prove2.me/submissions/62f4e1f5-cb00-40e7-9f82-8bbe9ef47c25

import Definitions.Def_RH1E6S01_D067_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0540 : RS5.BandZeros ((12596371491 : ℝ) / 65536) ((12601444601 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0540.s0 RH1E6S01_0540.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0540.s0 RH1E6S01_0540.rest = RH1E6S01_0540.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0540.s0 :: RH1E6S01_0540.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0540.s0.t = ((12596371491 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0540.s0]
  have e1 : RH1E6S01_0540.sL.t = ((12601444601 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0540.sL]
  rw [e0, e1] at h
  exact h

theorem band_0541 : RS5.BandZeros ((12601444601 : ℝ) / 65536) ((12606487614 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0541.s0 RH1E6S01_0541.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0541.s0 RH1E6S01_0541.rest = RH1E6S01_0541.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0541.s0 :: RH1E6S01_0541.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0541.s0.t = ((12601444601 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0541.s0]
  have e1 : RH1E6S01_0541.sL.t = ((12606487614 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0541.sL]
  rw [e0, e1] at h
  exact h

theorem part_067_2 : RS5.BandZeros ((12596371491 : ℝ) / 65536) ((12606487614 : ℝ) / 65536) 254 := by
  have g0 := band_0540
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0541
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12596371491 : ℝ) / 65536) ((12606487614 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_067_2 <;> assumption
