-- Prove2me | solution 1 for RH1E6S09.part_076_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T15:02:01.309766+00:00
-- url     : https://prove2.me/submissions/79dda1c5-29c3-4e8f-b61f-ca1c5aa4e07a

import Definitions.Def_RH1E6S09_D076_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0608 : RS5.BandZeros ((38829598299 : ℝ) / 65536) ((38834176529 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0608.s0 RH1E6S09_0608.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0608.s0 RH1E6S09_0608.rest = RH1E6S09_0608.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0608.s0 :: RH1E6S09_0608.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0608.s0.t = ((38829598299 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0608.s0]
  have e1 : RH1E6S09_0608.sL.t = ((38834176529 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0608.sL]
  rw [e0, e1] at h
  exact h

theorem band_0609 : RS5.BandZeros ((38834176529 : ℝ) / 65536) ((38838717062 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0609.s0 RH1E6S09_0609.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0609.s0 RH1E6S09_0609.rest = RH1E6S09_0609.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0609.s0 :: RH1E6S09_0609.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0609.s0.t = ((38834176529 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0609.s0]
  have e1 : RH1E6S09_0609.sL.t = ((38838717062 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0609.sL]
  rw [e0, e1] at h
  exact h

theorem part_076_0 : RS5.BandZeros ((38829598299 : ℝ) / 65536) ((38838717062 : ℝ) / 65536) 254 := by
  have g0 := band_0608
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0609
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38829598299 : ℝ) / 65536) ((38838717062 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_076_0 <;> assumption
