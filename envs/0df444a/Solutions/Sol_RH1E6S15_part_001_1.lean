-- Prove2me | solution 1 for RH1E6S15.part_001_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:49:56.66442+00:00
-- url     : https://prove2.me/submissions/b01456a9-0fb1-4ffb-b5ab-c1df4020131d

import Definitions.Def_RH1E6S15_D001_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0010 : RS5.BandZeros ((55749834647 : ℝ) / 65536) ((55754243055 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0010.s0 RH1E6S15_0010.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0010.s0 RH1E6S15_0010.rest = RH1E6S15_0010.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0010.s0 :: RH1E6S15_0010.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0010.s0.t = ((55749834647 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0010.s0]
  have e1 : RH1E6S15_0010.sL.t = ((55754243055 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0010.sL]
  rw [e0, e1] at h
  exact h

theorem band_0011 : RS5.BandZeros ((55754243055 : ℝ) / 65536) ((55758674032 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0011.s0 RH1E6S15_0011.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0011.s0 RH1E6S15_0011.rest = RH1E6S15_0011.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0011.s0 :: RH1E6S15_0011.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0011.s0.t = ((55754243055 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0011.s0]
  have e1 : RH1E6S15_0011.sL.t = ((55758674032 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0011.sL]
  rw [e0, e1] at h
  exact h

theorem part_001_1 : RS5.BandZeros ((55749834647 : ℝ) / 65536) ((55758674032 : ℝ) / 65536) 254 := by
  have g0 := band_0010
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0011
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((55749834647 : ℝ) / 65536) ((55758674032 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_001_1 <;> assumption
