-- Prove2me | solution 1 for RH1E6S03.part_039_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:42:41.978354+00:00
-- url     : https://prove2.me/submissions/38af90ac-d7ba-4d0a-bfdd-cc0697a752b1

import Definitions.Def_RH1E6S03_D039_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0316 : RS5.BandZeros ((17937520659 : ℝ) / 65536) ((17942406648 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0316.s0 RH1E6S03_0316.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0316.s0 RH1E6S03_0316.rest = RH1E6S03_0316.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0316.s0 :: RH1E6S03_0316.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0316.s0.t = ((17937520659 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0316.s0]
  have e1 : RH1E6S03_0316.sL.t = ((17942406648 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0316.sL]
  rw [e0, e1] at h
  exact h

theorem band_0317 : RS5.BandZeros ((17942406648 : ℝ) / 65536) ((17947311787 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0317.s0 RH1E6S03_0317.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0317.s0 RH1E6S03_0317.rest = RH1E6S03_0317.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0317.s0 :: RH1E6S03_0317.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0317.s0.t = ((17942406648 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0317.s0]
  have e1 : RH1E6S03_0317.sL.t = ((17947311787 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0317.sL]
  rw [e0, e1] at h
  exact h

theorem part_039_2 : RS5.BandZeros ((17937520659 : ℝ) / 65536) ((17947311787 : ℝ) / 65536) 254 := by
  have g0 := band_0316
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0317
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17937520659 : ℝ) / 65536) ((17947311787 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_039_2 <;> assumption
