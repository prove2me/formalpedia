-- Prove2me | solution 1 for RH1E6S08.part_056_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T06:40:48.059696+00:00
-- url     : https://prove2.me/submissions/2c88d38c-0eae-4659-8890-6ce64359373d

import Definitions.Def_RH1E6S08_D056_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0448 : RS5.BandZeros ((34838506069 : ℝ) / 65536) ((34843109084 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0448.s0 RH1E6S08_0448.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0448.s0 RH1E6S08_0448.rest = RH1E6S08_0448.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0448.s0 :: RH1E6S08_0448.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0448.s0.t = ((34838506069 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0448.s0]
  have e1 : RH1E6S08_0448.sL.t = ((34843109084 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0448.sL]
  rw [e0, e1] at h
  exact h

theorem band_0449 : RS5.BandZeros ((34843109084 : ℝ) / 65536) ((34847713443 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0449.s0 RH1E6S08_0449.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0449.s0 RH1E6S08_0449.rest = RH1E6S08_0449.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0449.s0 :: RH1E6S08_0449.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0449.s0.t = ((34843109084 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0449.s0]
  have e1 : RH1E6S08_0449.sL.t = ((34847713443 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0449.sL]
  rw [e0, e1] at h
  exact h

theorem part_056_0 : RS5.BandZeros ((34838506069 : ℝ) / 65536) ((34847713443 : ℝ) / 65536) 254 := by
  have g0 := band_0448
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0449
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((34838506069 : ℝ) / 65536) ((34847713443 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_056_0 <;> assumption
