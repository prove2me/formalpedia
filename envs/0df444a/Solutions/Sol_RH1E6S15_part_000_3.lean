-- Prove2me | solution 1 for RH1E6S15.part_000_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:46:26.387967+00:00
-- url     : https://prove2.me/submissions/c96a875d-77f3-4f71-a433-ca8ced177d49

import Definitions.Def_RH1E6S15_D000_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0006 : RS5.BandZeros ((55732111590 : ℝ) / 65536) ((55736551576 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0006.s0 RH1E6S15_0006.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0006.s0 RH1E6S15_0006.rest = RH1E6S15_0006.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0006.s0 :: RH1E6S15_0006.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0006.s0.t = ((55732111590 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0006.s0]
  have e1 : RH1E6S15_0006.sL.t = ((55736551576 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0006.sL]
  rw [e0, e1] at h
  exact h

theorem band_0007 : RS5.BandZeros ((55736551576 : ℝ) / 65536) ((55740970873 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0007.s0 RH1E6S15_0007.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0007.s0 RH1E6S15_0007.rest = RH1E6S15_0007.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0007.s0 :: RH1E6S15_0007.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0007.s0.t = ((55736551576 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0007.s0]
  have e1 : RH1E6S15_0007.sL.t = ((55740970873 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0007.sL]
  rw [e0, e1] at h
  exact h

theorem part_000_3 : RS5.BandZeros ((55732111590 : ℝ) / 65536) ((55740970873 : ℝ) / 65536) 254 := by
  have g0 := band_0006
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0007
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((55732111590 : ℝ) / 65536) ((55740970873 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_000_3 <;> assumption
