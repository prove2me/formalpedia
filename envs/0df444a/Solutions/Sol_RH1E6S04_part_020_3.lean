-- Prove2me | solution 1 for RH1E6S04.part_020_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:10:31.127918+00:00
-- url     : https://prove2.me/submissions/09e7335e-d08d-4ead-83d9-e9b4a8b52104

import Definitions.Def_RH1E6S04_D020_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0166 : RS5.BandZeros ((20465075602 : ℝ) / 65536) ((20469902038 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0166.s0 RH1E6S04_0166.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0166.s0 RH1E6S04_0166.rest = RH1E6S04_0166.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0166.s0 :: RH1E6S04_0166.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0166.s0.t = ((20465075602 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0166.s0]
  have e1 : RH1E6S04_0166.sL.t = ((20469902038 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0166.sL]
  rw [e0, e1] at h
  exact h

theorem band_0167 : RS5.BandZeros ((20469902038 : ℝ) / 65536) ((20474737888 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0167.s0 RH1E6S04_0167.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0167.s0 RH1E6S04_0167.rest = RH1E6S04_0167.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0167.s0 :: RH1E6S04_0167.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0167.s0.t = ((20469902038 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0167.s0]
  have e1 : RH1E6S04_0167.sL.t = ((20474737888 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0167.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_3 : RS5.BandZeros ((20465075602 : ℝ) / 65536) ((20474737888 : ℝ) / 65536) 254 := by
  have g0 := band_0166
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0167
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20465075602 : ℝ) / 65536) ((20474737888 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_020_3 <;> assumption
