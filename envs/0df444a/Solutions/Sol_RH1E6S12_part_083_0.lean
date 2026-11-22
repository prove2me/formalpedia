-- Prove2me | solution 1 for RH1E6S12.part_083_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:19:06.964425+00:00
-- url     : https://prove2.me/submissions/1c6440da-c98d-4ee1-a282-fc50e25439ad

import Definitions.Def_RH1E6S12_D083_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0664 : RS5.BandZeros ((48855131180 : ℝ) / 65536) ((48859613265 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0664.s0 RH1E6S12_0664.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0664.s0 RH1E6S12_0664.rest = RH1E6S12_0664.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0664.s0 :: RH1E6S12_0664.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0664.s0.t = ((48855131180 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0664.s0]
  have e1 : RH1E6S12_0664.sL.t = ((48859613265 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0664.sL]
  rw [e0, e1] at h
  exact h

theorem band_0665 : RS5.BandZeros ((48859613265 : ℝ) / 65536) ((48864073924 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0665.s0 RH1E6S12_0665.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0665.s0 RH1E6S12_0665.rest = RH1E6S12_0665.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0665.s0 :: RH1E6S12_0665.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0665.s0.t = ((48859613265 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0665.s0]
  have e1 : RH1E6S12_0665.sL.t = ((48864073924 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0665.sL]
  rw [e0, e1] at h
  exact h

theorem part_083_0 : RS5.BandZeros ((48855131180 : ℝ) / 65536) ((48864073924 : ℝ) / 65536) 254 := by
  have g0 := band_0664
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0665
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48855131180 : ℝ) / 65536) ((48864073924 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_083_0 <;> assumption
