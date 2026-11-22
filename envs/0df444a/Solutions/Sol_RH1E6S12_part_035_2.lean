-- Prove2me | solution 1 for RH1E6S12.part_035_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T09:09:14.140504+00:00
-- url     : https://prove2.me/submissions/2545b8da-32ee-4c25-8d7b-af031b8803d1

import Definitions.Def_RH1E6S12_D035_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0284 : RS5.BandZeros ((47151738434 : ℝ) / 65536) ((47156210231 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0284.s0 RH1E6S12_0284.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0284.s0 RH1E6S12_0284.rest = RH1E6S12_0284.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0284.s0 :: RH1E6S12_0284.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0284.s0.t = ((47151738434 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0284.s0]
  have e1 : RH1E6S12_0284.sL.t = ((47156210231 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0284.sL]
  rw [e0, e1] at h
  exact h

theorem band_0285 : RS5.BandZeros ((47156210231 : ℝ) / 65536) ((47160702812 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0285.s0 RH1E6S12_0285.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0285.s0 RH1E6S12_0285.rest = RH1E6S12_0285.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0285.s0 :: RH1E6S12_0285.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0285.s0.t = ((47156210231 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0285.s0]
  have e1 : RH1E6S12_0285.sL.t = ((47160702812 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0285.sL]
  rw [e0, e1] at h
  exact h

theorem part_035_2 : RS5.BandZeros ((47151738434 : ℝ) / 65536) ((47160702812 : ℝ) / 65536) 254 := by
  have g0 := band_0284
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0285
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47151738434 : ℝ) / 65536) ((47160702812 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_035_2 <;> assumption
