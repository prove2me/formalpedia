-- Prove2me | solution 1 for RH1E6S14.part_025_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:01:47.699796+00:00
-- url     : https://prove2.me/submissions/016e8762-6638-46ba-87ee-51b93ed59471

import Definitions.Def_RH1E6S14_D025_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0206 : RS5.BandZeros ((53344601869 : ℝ) / 65536) ((53349043294 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0206.s0 RH1E6S14_0206.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0206.s0 RH1E6S14_0206.rest = RH1E6S14_0206.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0206.s0 :: RH1E6S14_0206.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0206.s0.t = ((53344601869 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0206.s0]
  have e1 : RH1E6S14_0206.sL.t = ((53349043294 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0206.sL]
  rw [e0, e1] at h
  exact h

theorem band_0207 : RS5.BandZeros ((53349043294 : ℝ) / 65536) ((53353489783 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0207.s0 RH1E6S14_0207.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0207.s0 RH1E6S14_0207.rest = RH1E6S14_0207.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0207.s0 :: RH1E6S14_0207.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0207.s0.t = ((53349043294 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0207.s0]
  have e1 : RH1E6S14_0207.sL.t = ((53353489783 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0207.sL]
  rw [e0, e1] at h
  exact h

theorem part_025_3 : RS5.BandZeros ((53344601869 : ℝ) / 65536) ((53353489783 : ℝ) / 65536) 254 := by
  have g0 := band_0206
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0207
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53344601869 : ℝ) / 65536) ((53353489783 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_025_3 <;> assumption
