-- Prove2me | solution 1 for RH1E6S15.part_001_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:49:58.642552+00:00
-- url     : https://prove2.me/submissions/916c54ba-37cc-4f53-a28f-6c2958c35cca

import Definitions.Def_RH1E6S15_D001_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0012 : RS5.BandZeros ((55758674032 : ℝ) / 65536) ((55763094630 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0012.s0 RH1E6S15_0012.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0012.s0 RH1E6S15_0012.rest = RH1E6S15_0012.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0012.s0 :: RH1E6S15_0012.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0012.s0.t = ((55758674032 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0012.s0]
  have e1 : RH1E6S15_0012.sL.t = ((55763094630 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0012.sL]
  rw [e0, e1] at h
  exact h

theorem band_0013 : RS5.BandZeros ((55763094630 : ℝ) / 65536) ((55767533389 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0013.s0 RH1E6S15_0013.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0013.s0 RH1E6S15_0013.rest = RH1E6S15_0013.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0013.s0 :: RH1E6S15_0013.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0013.s0.t = ((55763094630 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0013.s0]
  have e1 : RH1E6S15_0013.sL.t = ((55767533389 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0013.sL]
  rw [e0, e1] at h
  exact h

theorem part_001_2 : RS5.BandZeros ((55758674032 : ℝ) / 65536) ((55767533389 : ℝ) / 65536) 254 := by
  have g0 := band_0012
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0013
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((55758674032 : ℝ) / 65536) ((55767533389 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_001_2 <;> assumption
