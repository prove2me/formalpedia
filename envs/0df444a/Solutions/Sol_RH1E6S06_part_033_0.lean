-- Prove2me | solution 1 for RH1E6S06.part_033_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:35:41.473215+00:00
-- url     : https://prove2.me/submissions/39b920c0-24bf-44e4-bd9d-37f76aaaf079

import Definitions.Def_RH1E6S06_D033_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0264 : RS5.BandZeros ((27459886807 : ℝ) / 65536) ((27464609833 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0264.s0 RH1E6S06_0264.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0264.s0 RH1E6S06_0264.rest = RH1E6S06_0264.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0264.s0 :: RH1E6S06_0264.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0264.s0.t = ((27459886807 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0264.s0]
  have e1 : RH1E6S06_0264.sL.t = ((27464609833 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0264.sL]
  rw [e0, e1] at h
  exact h

theorem band_0265 : RS5.BandZeros ((27464609833 : ℝ) / 65536) ((27469300432 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0265.s0 RH1E6S06_0265.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0265.s0 RH1E6S06_0265.rest = RH1E6S06_0265.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0265.s0 :: RH1E6S06_0265.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0265.s0.t = ((27464609833 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0265.s0]
  have e1 : RH1E6S06_0265.sL.t = ((27469300432 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0265.sL]
  rw [e0, e1] at h
  exact h

theorem part_033_0 : RS5.BandZeros ((27459886807 : ℝ) / 65536) ((27469300432 : ℝ) / 65536) 254 := by
  have g0 := band_0264
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0265
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27459886807 : ℝ) / 65536) ((27469300432 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_033_0 <;> assumption
