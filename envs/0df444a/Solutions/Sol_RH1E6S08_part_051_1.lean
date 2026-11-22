-- Prove2me | solution 1 for RH1E6S08.part_051_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T06:27:23.799824+00:00
-- url     : https://prove2.me/submissions/193eb013-974b-44a0-9d75-9d9d8e12dd6b

import Definitions.Def_RH1E6S08_D051_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0410 : RS5.BandZeros ((34663317239 : ℝ) / 65536) ((34667921450 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0410.s0 RH1E6S08_0410.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0410.s0 RH1E6S08_0410.rest = RH1E6S08_0410.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0410.s0 :: RH1E6S08_0410.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0410.s0.t = ((34663317239 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0410.s0]
  have e1 : RH1E6S08_0410.sL.t = ((34667921450 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0410.sL]
  rw [e0, e1] at h
  exact h

theorem band_0411 : RS5.BandZeros ((34667921450 : ℝ) / 65536) ((34672525350 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0411.s0 RH1E6S08_0411.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0411.s0 RH1E6S08_0411.rest = RH1E6S08_0411.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0411.s0 :: RH1E6S08_0411.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0411.s0.t = ((34667921450 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0411.s0]
  have e1 : RH1E6S08_0411.sL.t = ((34672525350 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0411.sL]
  rw [e0, e1] at h
  exact h

theorem part_051_1 : RS5.BandZeros ((34663317239 : ℝ) / 65536) ((34672525350 : ℝ) / 65536) 254 := by
  have g0 := band_0410
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0411
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((34663317239 : ℝ) / 65536) ((34672525350 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_051_1 <;> assumption
