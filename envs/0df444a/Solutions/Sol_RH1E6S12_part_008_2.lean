-- Prove2me | solution 1 for RH1E6S12.part_008_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:51:01.94828+00:00
-- url     : https://prove2.me/submissions/cb68623e-fbef-4f18-ba6a-58017579d76a

import Definitions.Def_RH1E6S12_D008_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0068 : RS5.BandZeros ((46181127671 : ℝ) / 65536) ((46185630398 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0068.s0 RH1E6S12_0068.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0068.s0 RH1E6S12_0068.rest = RH1E6S12_0068.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0068.s0 :: RH1E6S12_0068.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0068.s0.t = ((46181127671 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0068.s0]
  have e1 : RH1E6S12_0068.sL.t = ((46185630398 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0068.sL]
  rw [e0, e1] at h
  exact h

theorem band_0069 : RS5.BandZeros ((46185630398 : ℝ) / 65536) ((46190116832 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0069.s0 RH1E6S12_0069.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0069.s0 RH1E6S12_0069.rest = RH1E6S12_0069.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0069.s0 :: RH1E6S12_0069.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0069.s0.t = ((46185630398 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0069.s0]
  have e1 : RH1E6S12_0069.sL.t = ((46190116832 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0069.sL]
  rw [e0, e1] at h
  exact h

theorem part_008_2 : RS5.BandZeros ((46181127671 : ℝ) / 65536) ((46190116832 : ℝ) / 65536) 254 := by
  have g0 := band_0068
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0069
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46181127671 : ℝ) / 65536) ((46190116832 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_008_2 <;> assumption
