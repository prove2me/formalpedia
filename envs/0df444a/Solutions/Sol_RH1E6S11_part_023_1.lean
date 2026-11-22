-- Prove2me | solution 1 for RH1E6S11.part_023_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T04:05:40.063524+00:00
-- url     : https://prove2.me/submissions/cebce42d-003d-4851-bb78-48d79fce9bc9

import Definitions.Def_RH1E6S11_D023_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0186 : RS5.BandZeros ((43440070933 : ℝ) / 65536) ((43444574426 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0186.s0 RH1E6S11_0186.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0186.s0 RH1E6S11_0186.rest = RH1E6S11_0186.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0186.s0 :: RH1E6S11_0186.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0186.s0.t = ((43440070933 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0186.s0]
  have e1 : RH1E6S11_0186.sL.t = ((43444574426 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0186.sL]
  rw [e0, e1] at h
  exact h

theorem band_0187 : RS5.BandZeros ((43444574426 : ℝ) / 65536) ((43449104580 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0187.s0 RH1E6S11_0187.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0187.s0 RH1E6S11_0187.rest = RH1E6S11_0187.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0187.s0 :: RH1E6S11_0187.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0187.s0.t = ((43444574426 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0187.s0]
  have e1 : RH1E6S11_0187.sL.t = ((43449104580 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0187.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_1 : RS5.BandZeros ((43440070933 : ℝ) / 65536) ((43449104580 : ℝ) / 65536) 254 := by
  have g0 := band_0186
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0187
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43440070933 : ℝ) / 65536) ((43449104580 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_023_1 <;> assumption
