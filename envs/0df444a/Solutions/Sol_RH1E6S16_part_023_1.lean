-- Prove2me | solution 1 for RH1E6S16.part_023_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:23:35.191196+00:00
-- url     : https://prove2.me/submissions/4f0b99ab-008d-4da4-b514-5c9c824e5642

import Definitions.Def_RH1E6S16_D023_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0186 : RS5.BandZeros ((59801223068 : ℝ) / 65536) ((59805604717 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0186.s0 RH1E6S16_0186.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0186.s0 RH1E6S16_0186.rest = RH1E6S16_0186.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0186.s0 :: RH1E6S16_0186.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0186.s0.t = ((59801223068 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0186.s0]
  have e1 : RH1E6S16_0186.sL.t = ((59805604717 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0186.sL]
  rw [e0, e1] at h
  exact h

theorem band_0187 : RS5.BandZeros ((59805604717 : ℝ) / 65536) ((59810019655 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0187.s0 RH1E6S16_0187.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0187.s0 RH1E6S16_0187.rest = RH1E6S16_0187.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0187.s0 :: RH1E6S16_0187.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0187.s0.t = ((59805604717 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0187.s0]
  have e1 : RH1E6S16_0187.sL.t = ((59810019655 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0187.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_1 : RS5.BandZeros ((59801223068 : ℝ) / 65536) ((59810019655 : ℝ) / 65536) 254 := by
  have g0 := band_0186
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0187
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59801223068 : ℝ) / 65536) ((59810019655 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_023_1 <;> assumption
