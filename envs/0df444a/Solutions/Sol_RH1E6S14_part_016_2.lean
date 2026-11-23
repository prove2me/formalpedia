-- Prove2me | solution 1 for RH1E6S14.part_016_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T03:23:44.688502+00:00
-- url     : https://prove2.me/submissions/0e7ec1be-7b91-447c-93d4-ebe3d33b82f8

import Definitions.Def_RH1E6S14_D016_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0132 : RS5.BandZeros ((53015778886 : ℝ) / 65536) ((53020210957 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0132.s0 RH1E6S14_0132.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0132.s0 RH1E6S14_0132.rest = RH1E6S14_0132.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0132.s0 :: RH1E6S14_0132.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0132.s0.t = ((53015778886 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0132.s0]
  have e1 : RH1E6S14_0132.sL.t = ((53020210957 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0132.sL]
  rw [e0, e1] at h
  exact h

theorem band_0133 : RS5.BandZeros ((53020210957 : ℝ) / 65536) ((53024674248 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0133.s0 RH1E6S14_0133.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0133.s0 RH1E6S14_0133.rest = RH1E6S14_0133.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0133.s0 :: RH1E6S14_0133.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0133.s0.t = ((53020210957 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0133.s0]
  have e1 : RH1E6S14_0133.sL.t = ((53024674248 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0133.sL]
  rw [e0, e1] at h
  exact h

theorem part_016_2 : RS5.BandZeros ((53015778886 : ℝ) / 65536) ((53024674248 : ℝ) / 65536) 254 := by
  have g0 := band_0132
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0133
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53015778886 : ℝ) / 65536) ((53024674248 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_016_2 <;> assumption
