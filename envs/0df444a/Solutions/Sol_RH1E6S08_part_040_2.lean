-- Prove2me | solution 1 for RH1E6S08.part_040_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T05:57:17.195658+00:00
-- url     : https://prove2.me/submissions/734e8469-2ec4-47af-84b2-be08d04c45a7

import Definitions.Def_RH1E6S08_D040_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0324 : RS5.BandZeros ((34266540603 : ℝ) / 65536) ((34271164472 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0324.s0 RH1E6S08_0324.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0324.s0 RH1E6S08_0324.rest = RH1E6S08_0324.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0324.s0 :: RH1E6S08_0324.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0324.s0.t = ((34266540603 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0324.s0]
  have e1 : RH1E6S08_0324.sL.t = ((34271164472 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0324.sL]
  rw [e0, e1] at h
  exact h

theorem band_0325 : RS5.BandZeros ((34271164472 : ℝ) / 65536) ((34275762494 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0325.s0 RH1E6S08_0325.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0325.s0 RH1E6S08_0325.rest = RH1E6S08_0325.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0325.s0 :: RH1E6S08_0325.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0325.s0.t = ((34271164472 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0325.s0]
  have e1 : RH1E6S08_0325.sL.t = ((34275762494 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0325.sL]
  rw [e0, e1] at h
  exact h

theorem part_040_2 : RS5.BandZeros ((34266540603 : ℝ) / 65536) ((34275762494 : ℝ) / 65536) 254 := by
  have g0 := band_0324
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0325
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((34266540603 : ℝ) / 65536) ((34275762494 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_040_2 <;> assumption
