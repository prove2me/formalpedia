-- Prove2me | solution 1 for RH1E6S12.part_043_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T09:30:13.187803+00:00
-- url     : https://prove2.me/submissions/2beed51f-be63-41a6-a49a-7857e0a4da54

import Definitions.Def_RH1E6S12_D043_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0348 : RS5.BandZeros ((47438973203 : ℝ) / 65536) ((47443464421 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0348.s0 RH1E6S12_0348.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0348.s0 RH1E6S12_0348.rest = RH1E6S12_0348.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0348.s0 :: RH1E6S12_0348.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0348.s0.t = ((47438973203 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0348.s0]
  have e1 : RH1E6S12_0348.sL.t = ((47443464421 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0348.sL]
  rw [e0, e1] at h
  exact h

theorem band_0349 : RS5.BandZeros ((47443464421 : ℝ) / 65536) ((47447952767 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0349.s0 RH1E6S12_0349.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0349.s0 RH1E6S12_0349.rest = RH1E6S12_0349.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0349.s0 :: RH1E6S12_0349.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0349.s0.t = ((47443464421 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0349.s0]
  have e1 : RH1E6S12_0349.sL.t = ((47447952767 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0349.sL]
  rw [e0, e1] at h
  exact h

theorem part_043_2 : RS5.BandZeros ((47438973203 : ℝ) / 65536) ((47447952767 : ℝ) / 65536) 254 := by
  have g0 := band_0348
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0349
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47438973203 : ℝ) / 65536) ((47447952767 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_043_2 <;> assumption
