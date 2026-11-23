-- Prove2me | solution 1 for RH1E6S17.part_028_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T21:05:57.570224+00:00
-- url     : https://prove2.me/submissions/3c919491-964b-42a6-a51c-4e5e5b8b0fa4

import Definitions.Def_RH1E6S17_D028_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0226 : RS5.BandZeros ((63249527104 : ℝ) / 65536) ((63253906163 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0226.s0 RH1E6S17_0226.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0226.s0 RH1E6S17_0226.rest = RH1E6S17_0226.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0226.s0 :: RH1E6S17_0226.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0226.s0.t = ((63249527104 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0226.s0]
  have e1 : RH1E6S17_0226.sL.t = ((63253906163 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0226.sL]
  rw [e0, e1] at h
  exact h

theorem band_0227 : RS5.BandZeros ((63253906163 : ℝ) / 65536) ((63258276576 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0227.s0 RH1E6S17_0227.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0227.s0 RH1E6S17_0227.rest = RH1E6S17_0227.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0227.s0 :: RH1E6S17_0227.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0227.s0.t = ((63253906163 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0227.s0]
  have e1 : RH1E6S17_0227.sL.t = ((63258276576 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0227.sL]
  rw [e0, e1] at h
  exact h

theorem part_028_1 : RS5.BandZeros ((63249527104 : ℝ) / 65536) ((63258276576 : ℝ) / 65536) 254 := by
  have g0 := band_0226
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0227
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63249527104 : ℝ) / 65536) ((63258276576 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_028_1 <;> assumption
