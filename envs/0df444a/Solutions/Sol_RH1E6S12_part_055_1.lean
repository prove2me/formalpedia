-- Prove2me | solution 1 for RH1E6S12.part_055_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T10:05:31.081257+00:00
-- url     : https://prove2.me/submissions/85802553-e9bd-4aef-9706-cb41ee48769d

import Definitions.Def_RH1E6S12_D055_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0442 : RS5.BandZeros ((47860614158 : ℝ) / 65536) ((47865097910 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0442.s0 RH1E6S12_0442.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0442.s0 RH1E6S12_0442.rest = RH1E6S12_0442.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0442.s0 :: RH1E6S12_0442.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0442.s0.t = ((47860614158 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0442.s0]
  have e1 : RH1E6S12_0442.sL.t = ((47865097910 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0442.sL]
  rw [e0, e1] at h
  exact h

theorem band_0443 : RS5.BandZeros ((47865097910 : ℝ) / 65536) ((47869576527 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0443.s0 RH1E6S12_0443.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0443.s0 RH1E6S12_0443.rest = RH1E6S12_0443.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0443.s0 :: RH1E6S12_0443.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0443.s0.t = ((47865097910 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0443.s0]
  have e1 : RH1E6S12_0443.sL.t = ((47869576527 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0443.sL]
  rw [e0, e1] at h
  exact h

theorem part_055_1 : RS5.BandZeros ((47860614158 : ℝ) / 65536) ((47869576527 : ℝ) / 65536) 254 := by
  have g0 := band_0442
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0443
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47860614158 : ℝ) / 65536) ((47869576527 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_055_1 <;> assumption
