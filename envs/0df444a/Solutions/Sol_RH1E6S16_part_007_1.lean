-- Prove2me | solution 1 for RH1E6S16.part_007_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T14:17:45.487671+00:00
-- url     : https://prove2.me/submissions/b37a603f-4934-44a9-af0b-744875e3e770

import Definitions.Def_RH1E6S16_D007_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0058 : RS5.BandZeros ((59237837367 : ℝ) / 65536) ((59242228007 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0058.s0 RH1E6S16_0058.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0058.s0 RH1E6S16_0058.rest = RH1E6S16_0058.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0058.s0 :: RH1E6S16_0058.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0058.s0.t = ((59237837367 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0058.s0]
  have e1 : RH1E6S16_0058.sL.t = ((59242228007 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0058.sL]
  rw [e0, e1] at h
  exact h

theorem band_0059 : RS5.BandZeros ((59242228007 : ℝ) / 65536) ((59246613863 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0059.s0 RH1E6S16_0059.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0059.s0 RH1E6S16_0059.rest = RH1E6S16_0059.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0059.s0 :: RH1E6S16_0059.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0059.s0.t = ((59242228007 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0059.s0]
  have e1 : RH1E6S16_0059.sL.t = ((59246613863 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0059.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_1 : RS5.BandZeros ((59237837367 : ℝ) / 65536) ((59246613863 : ℝ) / 65536) 254 := by
  have g0 := band_0058
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0059
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59237837367 : ℝ) / 65536) ((59246613863 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_007_1 <;> assumption
