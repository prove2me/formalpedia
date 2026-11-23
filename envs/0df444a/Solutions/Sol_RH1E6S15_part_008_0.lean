-- Prove2me | solution 1 for RH1E6S15.part_008_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T08:16:24.89187+00:00
-- url     : https://prove2.me/submissions/84c23d11-d786-4264-871f-a627ea8c2367

import Definitions.Def_RH1E6S15_D008_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0064 : RS5.BandZeros ((55988782582 : ℝ) / 65536) ((55993217742 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0064.s0 RH1E6S15_0064.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0064.s0 RH1E6S15_0064.rest = RH1E6S15_0064.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0064.s0 :: RH1E6S15_0064.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0064.s0.t = ((55988782582 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0064.s0]
  have e1 : RH1E6S15_0064.sL.t = ((55993217742 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0064.sL]
  rw [e0, e1] at h
  exact h

theorem band_0065 : RS5.BandZeros ((55993217742 : ℝ) / 65536) ((55997618128 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0065.s0 RH1E6S15_0065.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0065.s0 RH1E6S15_0065.rest = RH1E6S15_0065.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0065.s0 :: RH1E6S15_0065.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0065.s0.t = ((55993217742 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0065.s0]
  have e1 : RH1E6S15_0065.sL.t = ((55997618128 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0065.sL]
  rw [e0, e1] at h
  exact h

theorem part_008_0 : RS5.BandZeros ((55988782582 : ℝ) / 65536) ((55997618128 : ℝ) / 65536) 254 := by
  have g0 := band_0064
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0065
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((55988782582 : ℝ) / 65536) ((55997618128 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_008_0 <;> assumption
