-- Prove2me | solution 1 for RH1E6S15.part_048_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:44:12.867257+00:00
-- url     : https://prove2.me/submissions/7e87ee36-1d49-4a96-861a-f51c82a00c91

import Definitions.Def_RH1E6S15_D048_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0386 : RS5.BandZeros ((57411876105 : ℝ) / 65536) ((57416283122 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0386.s0 RH1E6S15_0386.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0386.s0 RH1E6S15_0386.rest = RH1E6S15_0386.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0386.s0 :: RH1E6S15_0386.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0386.s0.t = ((57411876105 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0386.s0]
  have e1 : RH1E6S15_0386.sL.t = ((57416283122 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0386.sL]
  rw [e0, e1] at h
  exact h

theorem band_0387 : RS5.BandZeros ((57416283122 : ℝ) / 65536) ((57420706581 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0387.s0 RH1E6S15_0387.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0387.s0 RH1E6S15_0387.rest = RH1E6S15_0387.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0387.s0 :: RH1E6S15_0387.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0387.s0.t = ((57416283122 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0387.s0]
  have e1 : RH1E6S15_0387.sL.t = ((57420706581 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0387.sL]
  rw [e0, e1] at h
  exact h

theorem part_048_1 : RS5.BandZeros ((57411876105 : ℝ) / 65536) ((57420706581 : ℝ) / 65536) 254 := by
  have g0 := band_0386
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0387
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57411876105 : ℝ) / 65536) ((57420706581 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_048_1 <;> assumption
