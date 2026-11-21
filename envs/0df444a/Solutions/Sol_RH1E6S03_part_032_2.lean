-- Prove2me | solution 1 for RH1E6S03.part_032_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:25:35.249193+00:00
-- url     : https://prove2.me/submissions/ad27504c-3d92-4fa2-8dc6-93afdb184706

import Definitions.Def_RH1E6S03_D032_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0260 : RS5.BandZeros ((17663174276 : ℝ) / 65536) ((17668067325 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0260.s0 RH1E6S03_0260.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0260.s0 RH1E6S03_0260.rest = RH1E6S03_0260.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0260.s0 :: RH1E6S03_0260.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0260.s0.t = ((17663174276 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0260.s0]
  have e1 : RH1E6S03_0260.sL.t = ((17668067325 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0260.sL]
  rw [e0, e1] at h
  exact h

theorem band_0261 : RS5.BandZeros ((17668067325 : ℝ) / 65536) ((17672979548 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0261.s0 RH1E6S03_0261.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0261.s0 RH1E6S03_0261.rest = RH1E6S03_0261.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0261.s0 :: RH1E6S03_0261.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0261.s0.t = ((17668067325 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0261.s0]
  have e1 : RH1E6S03_0261.sL.t = ((17672979548 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0261.sL]
  rw [e0, e1] at h
  exact h

theorem part_032_2 : RS5.BandZeros ((17663174276 : ℝ) / 65536) ((17672979548 : ℝ) / 65536) 254 := by
  have g0 := band_0260
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0261
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17663174276 : ℝ) / 65536) ((17672979548 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_032_2 <;> assumption
