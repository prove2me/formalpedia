-- Prove2me | solution 1 for RH1E6S03.part_045_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:54:58.929495+00:00
-- url     : https://prove2.me/submissions/16cc2ebc-f8f7-4205-a698-289031f4b501

import Definitions.Def_RH1E6S03_D045_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0360 : RS5.BandZeros ((18152800895 : ℝ) / 65536) ((18157710313 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0360.s0 RH1E6S03_0360.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0360.s0 RH1E6S03_0360.rest = RH1E6S03_0360.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0360.s0 :: RH1E6S03_0360.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0360.s0.t = ((18152800895 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0360.s0]
  have e1 : RH1E6S03_0360.sL.t = ((18157710313 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0360.sL]
  rw [e0, e1] at h
  exact h

theorem band_0361 : RS5.BandZeros ((18157710313 : ℝ) / 65536) ((18162590730 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0361.s0 RH1E6S03_0361.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0361.s0 RH1E6S03_0361.rest = RH1E6S03_0361.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0361.s0 :: RH1E6S03_0361.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0361.s0.t = ((18157710313 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0361.s0]
  have e1 : RH1E6S03_0361.sL.t = ((18162590730 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0361.sL]
  rw [e0, e1] at h
  exact h

theorem part_045_0 : RS5.BandZeros ((18152800895 : ℝ) / 65536) ((18162590730 : ℝ) / 65536) 254 := by
  have g0 := band_0360
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0361
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18152800895 : ℝ) / 65536) ((18162590730 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_045_0 <;> assumption
