-- Prove2me | solution 1 for RH1E6S12.part_005_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:39:54.96181+00:00
-- url     : https://prove2.me/submissions/913660a7-760a-4f7d-850e-6ed18d50677d

import Definitions.Def_RH1E6S12_D005_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0046 : RS5.BandZeros ((46082172623 : ℝ) / 65536) ((46086682529 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0046.s0 RH1E6S12_0046.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0046.s0 RH1E6S12_0046.rest = RH1E6S12_0046.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0046.s0 :: RH1E6S12_0046.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0046.s0.t = ((46082172623 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0046.s0]
  have e1 : RH1E6S12_0046.sL.t = ((46086682529 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0046.sL]
  rw [e0, e1] at h
  exact h

theorem band_0047 : RS5.BandZeros ((46086682529 : ℝ) / 65536) ((46091183027 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0047.s0 RH1E6S12_0047.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0047.s0 RH1E6S12_0047.rest = RH1E6S12_0047.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0047.s0 :: RH1E6S12_0047.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0047.s0.t = ((46086682529 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0047.s0]
  have e1 : RH1E6S12_0047.sL.t = ((46091183027 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0047.sL]
  rw [e0, e1] at h
  exact h

theorem part_005_3 : RS5.BandZeros ((46082172623 : ℝ) / 65536) ((46091183027 : ℝ) / 65536) 254 := by
  have g0 := band_0046
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0047
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46082172623 : ℝ) / 65536) ((46091183027 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_005_3 <;> assumption
