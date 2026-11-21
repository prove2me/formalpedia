-- Prove2me | solution 1 for RH1E6S08.part_017_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:42:56.585598+00:00
-- url     : https://prove2.me/submissions/f7194da9-7430-4715-8506-c2d01dc9309e

import Definitions.Def_RH1E6S08_D017_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0136 : RS5.BandZeros ((33397745163 : ℝ) / 65536) ((33402376812 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0136.s0 RH1E6S08_0136.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0136.s0 RH1E6S08_0136.rest = RH1E6S08_0136.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0136.s0 :: RH1E6S08_0136.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0136.s0.t = ((33397745163 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0136.s0]
  have e1 : RH1E6S08_0136.sL.t = ((33402376812 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0136.sL]
  rw [e0, e1] at h
  exact h

theorem band_0137 : RS5.BandZeros ((33402376812 : ℝ) / 65536) ((33407006475 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0137.s0 RH1E6S08_0137.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0137.s0 RH1E6S08_0137.rest = RH1E6S08_0137.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0137.s0 :: RH1E6S08_0137.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0137.s0.t = ((33402376812 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0137.s0]
  have e1 : RH1E6S08_0137.sL.t = ((33407006475 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0137.sL]
  rw [e0, e1] at h
  exact h

theorem part_017_0 : RS5.BandZeros ((33397745163 : ℝ) / 65536) ((33407006475 : ℝ) / 65536) 254 := by
  have g0 := band_0136
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0137
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33397745163 : ℝ) / 65536) ((33407006475 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_017_0 <;> assumption
