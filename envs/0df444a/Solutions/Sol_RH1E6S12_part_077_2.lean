-- Prove2me | solution 1 for RH1E6S12.part_077_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:04:35.0898+00:00
-- url     : https://prove2.me/submissions/dad5c86c-f624-4773-816e-cdd55d477833

import Definitions.Def_RH1E6S12_D077_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0620 : RS5.BandZeros ((48658163073 : ℝ) / 65536) ((48662622989 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0620.s0 RH1E6S12_0620.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0620.s0 RH1E6S12_0620.rest = RH1E6S12_0620.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0620.s0 :: RH1E6S12_0620.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0620.s0.t = ((48658163073 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0620.s0]
  have e1 : RH1E6S12_0620.sL.t = ((48662622989 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0620.sL]
  rw [e0, e1] at h
  exact h

theorem band_0621 : RS5.BandZeros ((48662622989 : ℝ) / 65536) ((48667117807 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0621.s0 RH1E6S12_0621.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0621.s0 RH1E6S12_0621.rest = RH1E6S12_0621.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0621.s0 :: RH1E6S12_0621.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0621.s0.t = ((48662622989 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0621.s0]
  have e1 : RH1E6S12_0621.sL.t = ((48667117807 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0621.sL]
  rw [e0, e1] at h
  exact h

theorem part_077_2 : RS5.BandZeros ((48658163073 : ℝ) / 65536) ((48667117807 : ℝ) / 65536) 254 := by
  have g0 := band_0620
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0621
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48658163073 : ℝ) / 65536) ((48667117807 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_077_2 <;> assumption
