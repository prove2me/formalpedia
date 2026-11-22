-- Prove2me | solution 1 for RH1E6S10.part_070_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:07:25.870805+00:00
-- url     : https://prove2.me/submissions/cc99c1da-f5e1-427e-acbc-572d7b9805d7

import Definitions.Def_RH1E6S10_D070_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0562 : RS5.BandZeros ((41877598172 : ℝ) / 65536) ((41882107045 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0562.s0 RH1E6S10_0562.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0562.s0 RH1E6S10_0562.rest = RH1E6S10_0562.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0562.s0 :: RH1E6S10_0562.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0562.s0.t = ((41877598172 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0562.s0]
  have e1 : RH1E6S10_0562.sL.t = ((41882107045 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0562.sL]
  rw [e0, e1] at h
  exact h

theorem band_0563 : RS5.BandZeros ((41882107045 : ℝ) / 65536) ((41886651588 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0563.s0 RH1E6S10_0563.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0563.s0 RH1E6S10_0563.rest = RH1E6S10_0563.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0563.s0 :: RH1E6S10_0563.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0563.s0.t = ((41882107045 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0563.s0]
  have e1 : RH1E6S10_0563.sL.t = ((41886651588 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0563.sL]
  rw [e0, e1] at h
  exact h

theorem part_070_1 : RS5.BandZeros ((41877598172 : ℝ) / 65536) ((41886651588 : ℝ) / 65536) 254 := by
  have g0 := band_0562
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0563
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41877598172 : ℝ) / 65536) ((41886651588 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_070_1 <;> assumption
