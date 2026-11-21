-- Prove2me | solution 1 for RH1E6S06.part_030_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:29:51.729039+00:00
-- url     : https://prove2.me/submissions/6c531ea1-f4ff-4de5-b5f4-3ae94ffac2d3

import Definitions.Def_RH1E6S06_D030_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0244 : RS5.BandZeros ((27365734579 : ℝ) / 65536) ((27370449211 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0244.s0 RH1E6S06_0244.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0244.s0 RH1E6S06_0244.rest = RH1E6S06_0244.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0244.s0 :: RH1E6S06_0244.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0244.s0.t = ((27365734579 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0244.s0]
  have e1 : RH1E6S06_0244.sL.t = ((27370449211 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0244.sL]
  rw [e0, e1] at h
  exact h

theorem band_0245 : RS5.BandZeros ((27370449211 : ℝ) / 65536) ((27375136284 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0245.s0 RH1E6S06_0245.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0245.s0 RH1E6S06_0245.rest = RH1E6S06_0245.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0245.s0 :: RH1E6S06_0245.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0245.s0.t = ((27370449211 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0245.s0]
  have e1 : RH1E6S06_0245.sL.t = ((27375136284 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0245.sL]
  rw [e0, e1] at h
  exact h

theorem part_030_2 : RS5.BandZeros ((27365734579 : ℝ) / 65536) ((27375136284 : ℝ) / 65536) 254 := by
  have g0 := band_0244
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0245
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27365734579 : ℝ) / 65536) ((27375136284 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_030_2 <;> assumption
