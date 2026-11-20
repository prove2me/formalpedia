-- Prove2me | solution 1 for RH1E6S03.part_018_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:56:06.326467+00:00
-- url     : https://prove2.me/submissions/69468bb9-d2a9-4cee-8e9f-c58e358587fd

import Definitions.Def_RH1E6S03_D018_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0150 : RS5.BandZeros ((17123088172 : ℝ) / 65536) ((17127995505 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0150.s0 RH1E6S03_0150.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0150.s0 RH1E6S03_0150.rest = RH1E6S03_0150.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0150.s0 :: RH1E6S03_0150.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0150.s0.t = ((17123088172 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0150.s0]
  have e1 : RH1E6S03_0150.sL.t = ((17127995505 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0150.sL]
  rw [e0, e1] at h
  exact h

theorem band_0151 : RS5.BandZeros ((17127995505 : ℝ) / 65536) ((17132922064 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0151.s0 RH1E6S03_0151.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0151.s0 RH1E6S03_0151.rest = RH1E6S03_0151.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0151.s0 :: RH1E6S03_0151.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0151.s0.t = ((17127995505 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0151.s0]
  have e1 : RH1E6S03_0151.sL.t = ((17132922064 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0151.sL]
  rw [e0, e1] at h
  exact h

theorem part_018_3 : RS5.BandZeros ((17123088172 : ℝ) / 65536) ((17132922064 : ℝ) / 65536) 254 := by
  have g0 := band_0150
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0151
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17123088172 : ℝ) / 65536) ((17132922064 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_018_3 <;> assumption
