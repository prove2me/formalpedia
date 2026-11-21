-- Prove2me | solution 1 for RH1E6S06.part_034_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:40:57.121504+00:00
-- url     : https://prove2.me/submissions/1f12b9ac-f24c-4070-ad13-91d0b5f28cb5

import Definitions.Def_RH1E6S06_D034_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0276 : RS5.BandZeros ((27516383027 : ℝ) / 65536) ((27521101045 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0276.s0 RH1E6S06_0276.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0276.s0 RH1E6S06_0276.rest = RH1E6S06_0276.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0276.s0 :: RH1E6S06_0276.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0276.s0.t = ((27516383027 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0276.s0]
  have e1 : RH1E6S06_0276.sL.t = ((27521101045 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0276.sL]
  rw [e0, e1] at h
  exact h

theorem band_0277 : RS5.BandZeros ((27521101045 : ℝ) / 65536) ((27525797153 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0277.s0 RH1E6S06_0277.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0277.s0 RH1E6S06_0277.rest = RH1E6S06_0277.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0277.s0 :: RH1E6S06_0277.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0277.s0.t = ((27521101045 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0277.s0]
  have e1 : RH1E6S06_0277.sL.t = ((27525797153 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0277.sL]
  rw [e0, e1] at h
  exact h

theorem part_034_2 : RS5.BandZeros ((27516383027 : ℝ) / 65536) ((27525797153 : ℝ) / 65536) 254 := by
  have g0 := band_0276
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0277
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27516383027 : ℝ) / 65536) ((27525797153 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_034_2 <;> assumption
