-- Prove2me | solution 1 for RH1E6S14.part_031_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:20:09.24196+00:00
-- url     : https://prove2.me/submissions/5569ad11-1bd8-424e-8e4d-af2ee28751e7

import Definitions.Def_RH1E6S14_D031_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0248 : RS5.BandZeros ((53531155180 : ℝ) / 65536) ((53535605018 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0248.s0 RH1E6S14_0248.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0248.s0 RH1E6S14_0248.rest = RH1E6S14_0248.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0248.s0 :: RH1E6S14_0248.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0248.s0.t = ((53531155180 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0248.s0]
  have e1 : RH1E6S14_0248.sL.t = ((53535605018 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0248.sL]
  rw [e0, e1] at h
  exact h

theorem band_0249 : RS5.BandZeros ((53535605018 : ℝ) / 65536) ((53540044138 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0249.s0 RH1E6S14_0249.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0249.s0 RH1E6S14_0249.rest = RH1E6S14_0249.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0249.s0 :: RH1E6S14_0249.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0249.s0.t = ((53535605018 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0249.s0]
  have e1 : RH1E6S14_0249.sL.t = ((53540044138 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0249.sL]
  rw [e0, e1] at h
  exact h

theorem part_031_0 : RS5.BandZeros ((53531155180 : ℝ) / 65536) ((53540044138 : ℝ) / 65536) 254 := by
  have g0 := band_0248
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0249
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53531155180 : ℝ) / 65536) ((53540044138 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_031_0 <;> assumption
