-- Prove2me | solution 1 for RH1E6S14.part_038_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:46:52.358076+00:00
-- url     : https://prove2.me/submissions/3e8030ee-6e4e-457c-8d48-53ac7e022357

import Definitions.Def_RH1E6S14_D038_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0308 : RS5.BandZeros ((53797576301 : ℝ) / 65536) ((53802013595 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0308.s0 RH1E6S14_0308.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0308.s0 RH1E6S14_0308.rest = RH1E6S14_0308.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0308.s0 :: RH1E6S14_0308.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0308.s0.t = ((53797576301 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0308.s0]
  have e1 : RH1E6S14_0308.sL.t = ((53802013595 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0308.sL]
  rw [e0, e1] at h
  exact h

theorem band_0309 : RS5.BandZeros ((53802013595 : ℝ) / 65536) ((53806461527 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0309.s0 RH1E6S14_0309.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0309.s0 RH1E6S14_0309.rest = RH1E6S14_0309.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0309.s0 :: RH1E6S14_0309.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0309.s0.t = ((53802013595 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0309.s0]
  have e1 : RH1E6S14_0309.sL.t = ((53806461527 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0309.sL]
  rw [e0, e1] at h
  exact h

theorem part_038_2 : RS5.BandZeros ((53797576301 : ℝ) / 65536) ((53806461527 : ℝ) / 65536) 254 := by
  have g0 := band_0308
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0309
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53797576301 : ℝ) / 65536) ((53806461527 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_038_2 <;> assumption
