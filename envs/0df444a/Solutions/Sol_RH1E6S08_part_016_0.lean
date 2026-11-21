-- Prove2me | solution 1 for RH1E6S08.part_016_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:40:16.02125+00:00
-- url     : https://prove2.me/submissions/352aa61f-3860-4064-9502-179b9548b572

import Definitions.Def_RH1E6S08_D016_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0128 : RS5.BandZeros ((33360746797 : ℝ) / 65536) ((33365366148 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0128.s0 RH1E6S08_0128.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0128.s0 RH1E6S08_0128.rest = RH1E6S08_0128.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0128.s0 :: RH1E6S08_0128.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0128.s0.t = ((33360746797 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0128.s0]
  have e1 : RH1E6S08_0128.sL.t = ((33365366148 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0128.sL]
  rw [e0, e1] at h
  exact h

theorem band_0129 : RS5.BandZeros ((33365366148 : ℝ) / 65536) ((33369994431 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0129.s0 RH1E6S08_0129.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0129.s0 RH1E6S08_0129.rest = RH1E6S08_0129.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0129.s0 :: RH1E6S08_0129.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0129.s0.t = ((33365366148 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0129.s0]
  have e1 : RH1E6S08_0129.sL.t = ((33369994431 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0129.sL]
  rw [e0, e1] at h
  exact h

theorem part_016_0 : RS5.BandZeros ((33360746797 : ℝ) / 65536) ((33369994431 : ℝ) / 65536) 254 := by
  have g0 := band_0128
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0129
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33360746797 : ℝ) / 65536) ((33369994431 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_016_0 <;> assumption
