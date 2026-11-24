-- Prove2me | solution 1 for RH1E6S17.part_070_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T23:30:21.55119+00:00
-- url     : https://prove2.me/submissions/499e26e2-3b5a-4fcd-9346-a33c7edf5cb1

import Definitions.Def_RH1E6S17_D070_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0562 : RS5.BandZeros ((64719484348 : ℝ) / 65536) ((64723837791 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0562.s0 RH1E6S17_0562.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0562.s0 RH1E6S17_0562.rest = RH1E6S17_0562.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0562.s0 :: RH1E6S17_0562.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0562.s0.t = ((64719484348 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0562.s0]
  have e1 : RH1E6S17_0562.sL.t = ((64723837791 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0562.sL]
  rw [e0, e1] at h
  exact h

theorem band_0563 : RS5.BandZeros ((64723837791 : ℝ) / 65536) ((64728217021 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0563.s0 RH1E6S17_0563.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0563.s0 RH1E6S17_0563.rest = RH1E6S17_0563.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0563.s0 :: RH1E6S17_0563.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0563.s0.t = ((64723837791 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0563.s0]
  have e1 : RH1E6S17_0563.sL.t = ((64728217021 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0563.sL]
  rw [e0, e1] at h
  exact h

theorem part_070_1 : RS5.BandZeros ((64719484348 : ℝ) / 65536) ((64728217021 : ℝ) / 65536) 254 := by
  have g0 := band_0562
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0563
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64719484348 : ℝ) / 65536) ((64728217021 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_070_1 <;> assumption
