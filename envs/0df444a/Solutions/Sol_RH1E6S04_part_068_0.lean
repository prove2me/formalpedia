-- Prove2me | solution 1 for RH1E6S04.part_068_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:58:01.20726+00:00
-- url     : https://prove2.me/submissions/cc58fe4c-8bf9-45ca-aa6d-d4ca59286cb4

import Definitions.Def_RH1E6S04_D068_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0544 : RS5.BandZeros ((22285809663 : ℝ) / 65536) ((22290607806 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0544.s0 RH1E6S04_0544.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0544.s0 RH1E6S04_0544.rest = RH1E6S04_0544.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0544.s0 :: RH1E6S04_0544.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0544.s0.t = ((22285809663 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0544.s0]
  have e1 : RH1E6S04_0544.sL.t = ((22290607806 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0544.sL]
  rw [e0, e1] at h
  exact h

theorem band_0545 : RS5.BandZeros ((22290607806 : ℝ) / 65536) ((22295405855 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0545.s0 RH1E6S04_0545.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0545.s0 RH1E6S04_0545.rest = RH1E6S04_0545.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0545.s0 :: RH1E6S04_0545.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0545.s0.t = ((22290607806 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0545.s0]
  have e1 : RH1E6S04_0545.sL.t = ((22295405855 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0545.sL]
  rw [e0, e1] at h
  exact h

theorem part_068_0 : RS5.BandZeros ((22285809663 : ℝ) / 65536) ((22295405855 : ℝ) / 65536) 254 := by
  have g0 := band_0544
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0545
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22285809663 : ℝ) / 65536) ((22295405855 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_068_0 <;> assumption
