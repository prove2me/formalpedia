-- Prove2me | solution 1 for RH1E6S12.part_043_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T09:35:54.358172+00:00
-- url     : https://prove2.me/submissions/d1e4dbdc-62f6-41b6-95b2-0925074f7f4c

import Definitions.Def_RH1E6S12_D043_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0350 : RS5.BandZeros ((47447952767 : ℝ) / 65536) ((47452434492 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0350.s0 RH1E6S12_0350.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0350.s0 RH1E6S12_0350.rest = RH1E6S12_0350.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0350.s0 :: RH1E6S12_0350.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0350.s0.t = ((47447952767 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0350.s0]
  have e1 : RH1E6S12_0350.sL.t = ((47452434492 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0350.sL]
  rw [e0, e1] at h
  exact h

theorem band_0351 : RS5.BandZeros ((47452434492 : ℝ) / 65536) ((47456922627 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0351.s0 RH1E6S12_0351.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0351.s0 RH1E6S12_0351.rest = RH1E6S12_0351.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0351.s0 :: RH1E6S12_0351.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0351.s0.t = ((47452434492 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0351.s0]
  have e1 : RH1E6S12_0351.sL.t = ((47456922627 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0351.sL]
  rw [e0, e1] at h
  exact h

theorem part_043_3 : RS5.BandZeros ((47447952767 : ℝ) / 65536) ((47456922627 : ℝ) / 65536) 254 := by
  have g0 := band_0350
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0351
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47447952767 : ℝ) / 65536) ((47456922627 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_043_3 <;> assumption
