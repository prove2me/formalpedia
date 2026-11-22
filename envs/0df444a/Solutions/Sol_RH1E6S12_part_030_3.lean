-- Prove2me | solution 1 for RH1E6S12.part_030_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T08:54:44.616687+00:00
-- url     : https://prove2.me/submissions/8d94431e-cc16-49a2-bac8-6733e51e2b3b

import Definitions.Def_RH1E6S12_D030_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0246 : RS5.BandZeros ((46981111256 : ℝ) / 65536) ((46985600937 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0246.s0 RH1E6S12_0246.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0246.s0 RH1E6S12_0246.rest = RH1E6S12_0246.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0246.s0 :: RH1E6S12_0246.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0246.s0.t = ((46981111256 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0246.s0]
  have e1 : RH1E6S12_0246.sL.t = ((46985600937 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0246.sL]
  rw [e0, e1] at h
  exact h

theorem band_0247 : RS5.BandZeros ((46985600937 : ℝ) / 65536) ((46990095132 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0247.s0 RH1E6S12_0247.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0247.s0 RH1E6S12_0247.rest = RH1E6S12_0247.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0247.s0 :: RH1E6S12_0247.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0247.s0.t = ((46985600937 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0247.s0]
  have e1 : RH1E6S12_0247.sL.t = ((46990095132 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0247.sL]
  rw [e0, e1] at h
  exact h

theorem part_030_3 : RS5.BandZeros ((46981111256 : ℝ) / 65536) ((46990095132 : ℝ) / 65536) 254 := by
  have g0 := band_0246
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0247
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46981111256 : ℝ) / 65536) ((46990095132 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_030_3 <;> assumption
