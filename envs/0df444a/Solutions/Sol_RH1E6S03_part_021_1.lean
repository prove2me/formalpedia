-- Prove2me | solution 1 for RH1E6S03.part_021_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:00:59.119372+00:00
-- url     : https://prove2.me/submissions/3ec9567e-1f53-4e09-ab08-555814732110

import Definitions.Def_RH1E6S03_D021_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0170 : RS5.BandZeros ((17221403262 : ℝ) / 65536) ((17226307955 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0170.s0 RH1E6S03_0170.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0170.s0 RH1E6S03_0170.rest = RH1E6S03_0170.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0170.s0 :: RH1E6S03_0170.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0170.s0.t = ((17221403262 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0170.s0]
  have e1 : RH1E6S03_0170.sL.t = ((17226307955 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0170.sL]
  rw [e0, e1] at h
  exact h

theorem band_0171 : RS5.BandZeros ((17226307955 : ℝ) / 65536) ((17231212518 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0171.s0 RH1E6S03_0171.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0171.s0 RH1E6S03_0171.rest = RH1E6S03_0171.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0171.s0 :: RH1E6S03_0171.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0171.s0.t = ((17226307955 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0171.s0]
  have e1 : RH1E6S03_0171.sL.t = ((17231212518 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0171.sL]
  rw [e0, e1] at h
  exact h

theorem part_021_1 : RS5.BandZeros ((17221403262 : ℝ) / 65536) ((17231212518 : ℝ) / 65536) 254 := by
  have g0 := band_0170
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0171
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17221403262 : ℝ) / 65536) ((17231212518 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_021_1 <;> assumption
