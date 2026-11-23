-- Prove2me | solution 1 for RH1E6S14.part_058_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T05:50:07.019359+00:00
-- url     : https://prove2.me/submissions/451d37e5-35d6-44aa-973a-241554eb254a

import Definitions.Def_RH1E6S14_D058_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0470 : RS5.BandZeros ((54516341912 : ℝ) / 65536) ((54520751560 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0470.s0 RH1E6S14_0470.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0470.s0 RH1E6S14_0470.rest = RH1E6S14_0470.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0470.s0 :: RH1E6S14_0470.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0470.s0.t = ((54516341912 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0470.s0]
  have e1 : RH1E6S14_0470.sL.t = ((54520751560 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0470.sL]
  rw [e0, e1] at h
  exact h

theorem band_0471 : RS5.BandZeros ((54520751560 : ℝ) / 65536) ((54525185489 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0471.s0 RH1E6S14_0471.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0471.s0 RH1E6S14_0471.rest = RH1E6S14_0471.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0471.s0 :: RH1E6S14_0471.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0471.s0.t = ((54520751560 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0471.s0]
  have e1 : RH1E6S14_0471.sL.t = ((54525185489 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0471.sL]
  rw [e0, e1] at h
  exact h

theorem part_058_3 : RS5.BandZeros ((54516341912 : ℝ) / 65536) ((54525185489 : ℝ) / 65536) 254 := by
  have g0 := band_0470
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0471
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((54516341912 : ℝ) / 65536) ((54525185489 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_058_3 <;> assumption
