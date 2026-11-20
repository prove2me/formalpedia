-- Prove2me | solution 1 for RH1E6S00.part_063_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T22:54:52.119961+00:00
-- url     : https://prove2.me/submissions/e29615ee-1460-424e-ae06-dfb54f51fe1d

import Definitions.Def_RH1E6S00_D063_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0508 : RS5.BandZeros ((9248723784 : ℝ) / 65536) ((9253953263 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0508.s0 RH1E6S00_0508.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0508.s0 RH1E6S00_0508.rest = RH1E6S00_0508.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0508.s0 :: RH1E6S00_0508.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0508.s0.t = ((9248723784 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0508.s0]
  have e1 : RH1E6S00_0508.sL.t = ((9253953263 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0508.sL]
  rw [e0, e1] at h
  exact h

theorem band_0509 : RS5.BandZeros ((9253953263 : ℝ) / 65536) ((9259161901 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0509.s0 RH1E6S00_0509.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0509.s0 RH1E6S00_0509.rest = RH1E6S00_0509.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0509.s0 :: RH1E6S00_0509.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0509.s0.t = ((9253953263 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0509.s0]
  have e1 : RH1E6S00_0509.sL.t = ((9259161901 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0509.sL]
  rw [e0, e1] at h
  exact h

theorem part_063_2 : RS5.BandZeros ((9248723784 : ℝ) / 65536) ((9259161901 : ℝ) / 65536) 254 := by
  have g0 := band_0508
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0509
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9248723784 : ℝ) / 65536) ((9259161901 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_063_2 <;> assumption
