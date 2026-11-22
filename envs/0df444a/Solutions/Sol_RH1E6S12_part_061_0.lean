-- Prove2me | solution 1 for RH1E6S12.part_061_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T10:22:56.524491+00:00
-- url     : https://prove2.me/submissions/f5629037-a8e7-43e3-b521-fc4f0a33bf2e

import Definitions.Def_RH1E6S12_D061_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0488 : RS5.BandZeros ((48066819428 : ℝ) / 65536) ((48071310327 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0488.s0 RH1E6S12_0488.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0488.s0 RH1E6S12_0488.rest = RH1E6S12_0488.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0488.s0 :: RH1E6S12_0488.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0488.s0.t = ((48066819428 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0488.s0]
  have e1 : RH1E6S12_0488.sL.t = ((48071310327 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0488.sL]
  rw [e0, e1] at h
  exact h

theorem band_0489 : RS5.BandZeros ((48071310327 : ℝ) / 65536) ((48075783545 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0489.s0 RH1E6S12_0489.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0489.s0 RH1E6S12_0489.rest = RH1E6S12_0489.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0489.s0 :: RH1E6S12_0489.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0489.s0.t = ((48071310327 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0489.s0]
  have e1 : RH1E6S12_0489.sL.t = ((48075783545 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0489.sL]
  rw [e0, e1] at h
  exact h

theorem part_061_0 : RS5.BandZeros ((48066819428 : ℝ) / 65536) ((48075783545 : ℝ) / 65536) 254 := by
  have g0 := band_0488
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0489
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48066819428 : ℝ) / 65536) ((48075783545 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_061_0 <;> assumption
