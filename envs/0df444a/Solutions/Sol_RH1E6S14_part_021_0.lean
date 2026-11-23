-- Prove2me | solution 1 for RH1E6S14.part_021_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T03:41:13.633911+00:00
-- url     : https://prove2.me/submissions/caf4774f-d33c-4506-858d-c05b2f2b12cb

import Definitions.Def_RH1E6S14_D021_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0168 : RS5.BandZeros ((53175770433 : ℝ) / 65536) ((53180227000 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0168.s0 RH1E6S14_0168.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0168.s0 RH1E6S14_0168.rest = RH1E6S14_0168.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0168.s0 :: RH1E6S14_0168.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0168.s0.t = ((53175770433 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0168.s0]
  have e1 : RH1E6S14_0168.sL.t = ((53180227000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0168.sL]
  rw [e0, e1] at h
  exact h

theorem band_0169 : RS5.BandZeros ((53180227000 : ℝ) / 65536) ((53184664862 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0169.s0 RH1E6S14_0169.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0169.s0 RH1E6S14_0169.rest = RH1E6S14_0169.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0169.s0 :: RH1E6S14_0169.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0169.s0.t = ((53180227000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0169.s0]
  have e1 : RH1E6S14_0169.sL.t = ((53184664862 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0169.sL]
  rw [e0, e1] at h
  exact h

theorem part_021_0 : RS5.BandZeros ((53175770433 : ℝ) / 65536) ((53184664862 : ℝ) / 65536) 254 := by
  have g0 := band_0168
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0169
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53175770433 : ℝ) / 65536) ((53184664862 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_021_0 <;> assumption
