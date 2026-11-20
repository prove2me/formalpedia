-- Prove2me | solution 1 for RH1E6S00.part_065_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T22:59:25.343961+00:00
-- url     : https://prove2.me/submissions/ddf56fa9-348a-4894-969e-26b1e30a1e20

import Definitions.Def_RH1E6S00_D065_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0524 : RS5.BandZeros ((9332216472 : ℝ) / 65536) ((9337400208 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0524.s0 RH1E6S00_0524.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0524.s0 RH1E6S00_0524.rest = RH1E6S00_0524.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0524.s0 :: RH1E6S00_0524.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0524.s0.t = ((9332216472 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0524.s0]
  have e1 : RH1E6S00_0524.sL.t = ((9337400208 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0524.sL]
  rw [e0, e1] at h
  exact h

theorem band_0525 : RS5.BandZeros ((9337400208 : ℝ) / 65536) ((9342624714 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0525.s0 RH1E6S00_0525.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0525.s0 RH1E6S00_0525.rest = RH1E6S00_0525.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0525.s0 :: RH1E6S00_0525.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0525.s0.t = ((9337400208 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0525.s0]
  have e1 : RH1E6S00_0525.sL.t = ((9342624714 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0525.sL]
  rw [e0, e1] at h
  exact h

theorem part_065_2 : RS5.BandZeros ((9332216472 : ℝ) / 65536) ((9342624714 : ℝ) / 65536) 254 := by
  have g0 := band_0524
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0525
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9332216472 : ℝ) / 65536) ((9342624714 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_065_2 <;> assumption
