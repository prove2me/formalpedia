-- Prove2me | solution 1 for RH1E6S15.part_092_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:50:40.702811+00:00
-- url     : https://prove2.me/submissions/5aa3dda8-efff-4997-8303-f41cd040bc07

import Definitions.Def_RH1E6S15_D092_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0740 : RS5.BandZeros ((58972974176 : ℝ) / 65536) ((58977369936 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0740.s0 RH1E6S15_0740.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0740.s0 RH1E6S15_0740.rest = RH1E6S15_0740.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0740.s0 :: RH1E6S15_0740.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0740.s0.t = ((58972974176 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0740.s0]
  have e1 : RH1E6S15_0740.sL.t = ((58977369936 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0740.sL]
  rw [e0, e1] at h
  exact h

theorem band_0741 : RS5.BandZeros ((58977369936 : ℝ) / 65536) ((58981761998 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0741.s0 RH1E6S15_0741.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0741.s0 RH1E6S15_0741.rest = RH1E6S15_0741.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0741.s0 :: RH1E6S15_0741.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0741.s0.t = ((58977369936 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0741.s0]
  have e1 : RH1E6S15_0741.sL.t = ((58981761998 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0741.sL]
  rw [e0, e1] at h
  exact h

theorem part_092_2 : RS5.BandZeros ((58972974176 : ℝ) / 65536) ((58981761998 : ℝ) / 65536) 254 := by
  have g0 := band_0740
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0741
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58972974176 : ℝ) / 65536) ((58981761998 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_092_2 <;> assumption
