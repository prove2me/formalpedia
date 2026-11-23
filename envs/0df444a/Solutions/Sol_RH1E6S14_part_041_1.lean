-- Prove2me | solution 1 for RH1E6S14.part_041_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:53:11.587941+00:00
-- url     : https://prove2.me/submissions/82031697-c369-405b-9bea-35c641b13ec6

import Definitions.Def_RH1E6S14_D041_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0330 : RS5.BandZeros ((53895221380 : ℝ) / 65536) ((53899668658 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0330.s0 RH1E6S14_0330.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0330.s0 RH1E6S14_0330.rest = RH1E6S14_0330.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0330.s0 :: RH1E6S14_0330.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0330.s0.t = ((53895221380 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0330.s0]
  have e1 : RH1E6S14_0330.sL.t = ((53899668658 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0330.sL]
  rw [e0, e1] at h
  exact h

theorem band_0331 : RS5.BandZeros ((53899668658 : ℝ) / 65536) ((53904098430 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0331.s0 RH1E6S14_0331.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0331.s0 RH1E6S14_0331.rest = RH1E6S14_0331.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0331.s0 :: RH1E6S14_0331.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0331.s0.t = ((53899668658 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0331.s0]
  have e1 : RH1E6S14_0331.sL.t = ((53904098430 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0331.sL]
  rw [e0, e1] at h
  exact h

theorem part_041_1 : RS5.BandZeros ((53895221380 : ℝ) / 65536) ((53904098430 : ℝ) / 65536) 254 := by
  have g0 := band_0330
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0331
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53895221380 : ℝ) / 65536) ((53904098430 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_041_1 <;> assumption
