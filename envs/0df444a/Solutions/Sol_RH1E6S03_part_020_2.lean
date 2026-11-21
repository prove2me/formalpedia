-- Prove2me | solution 1 for RH1E6S03.part_020_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:00:52.750547+00:00
-- url     : https://prove2.me/submissions/a1e2ae39-09e2-4412-8b6a-f77b89c7bf3d

import Definitions.Def_RH1E6S03_D020_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0164 : RS5.BandZeros ((17191904612 : ℝ) / 65536) ((17196819771 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0164.s0 RH1E6S03_0164.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0164.s0 RH1E6S03_0164.rest = RH1E6S03_0164.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0164.s0 :: RH1E6S03_0164.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0164.s0.t = ((17191904612 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0164.s0]
  have e1 : RH1E6S03_0164.sL.t = ((17196819771 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0164.sL]
  rw [e0, e1] at h
  exact h

theorem band_0165 : RS5.BandZeros ((17196819771 : ℝ) / 65536) ((17201725123 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0165.s0 RH1E6S03_0165.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0165.s0 RH1E6S03_0165.rest = RH1E6S03_0165.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0165.s0 :: RH1E6S03_0165.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0165.s0.t = ((17196819771 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0165.s0]
  have e1 : RH1E6S03_0165.sL.t = ((17201725123 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0165.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_2 : RS5.BandZeros ((17191904612 : ℝ) / 65536) ((17201725123 : ℝ) / 65536) 254 := by
  have g0 := band_0164
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0165
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17191904612 : ℝ) / 65536) ((17201725123 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_020_2 <;> assumption
