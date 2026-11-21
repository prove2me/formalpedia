-- Prove2me | solution 1 for RH1E6S08.part_026_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T05:08:47.799667+00:00
-- url     : https://prove2.me/submissions/cb0bd081-eabe-4daa-a265-5a95ff7731db

import Definitions.Def_RH1E6S08_D026_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0210 : RS5.BandZeros ((33739949448 : ℝ) / 65536) ((33744580723 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0210.s0 RH1E6S08_0210.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0210.s0 RH1E6S08_0210.rest = RH1E6S08_0210.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0210.s0 :: RH1E6S08_0210.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0210.s0.t = ((33739949448 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0210.s0]
  have e1 : RH1E6S08_0210.sL.t = ((33744580723 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0210.sL]
  rw [e0, e1] at h
  exact h

theorem band_0211 : RS5.BandZeros ((33744580723 : ℝ) / 65536) ((33749206467 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0211.s0 RH1E6S08_0211.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0211.s0 RH1E6S08_0211.rest = RH1E6S08_0211.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0211.s0 :: RH1E6S08_0211.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0211.s0.t = ((33744580723 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0211.s0]
  have e1 : RH1E6S08_0211.sL.t = ((33749206467 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0211.sL]
  rw [e0, e1] at h
  exact h

theorem part_026_1 : RS5.BandZeros ((33739949448 : ℝ) / 65536) ((33749206467 : ℝ) / 65536) 254 := by
  have g0 := band_0210
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0211
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33739949448 : ℝ) / 65536) ((33749206467 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_026_1 <;> assumption
