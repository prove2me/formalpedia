-- Prove2me | solution 1 for RH1E6S04.part_054_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:27:47.026268+00:00
-- url     : https://prove2.me/submissions/a01990d1-a5e3-42d8-b135-ebcf3fe21d36

import Definitions.Def_RH1E6S04_D054_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0434 : RS5.BandZeros ((21757413998 : ℝ) / 65536) ((21762228643 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0434.s0 RH1E6S04_0434.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0434.s0 RH1E6S04_0434.rest = RH1E6S04_0434.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0434.s0 :: RH1E6S04_0434.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0434.s0.t = ((21757413998 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0434.s0]
  have e1 : RH1E6S04_0434.sL.t = ((21762228643 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0434.sL]
  rw [e0, e1] at h
  exact h

theorem band_0435 : RS5.BandZeros ((21762228643 : ℝ) / 65536) ((21767037274 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0435.s0 RH1E6S04_0435.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0435.s0 RH1E6S04_0435.rest = RH1E6S04_0435.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0435.s0 :: RH1E6S04_0435.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0435.s0.t = ((21762228643 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0435.s0]
  have e1 : RH1E6S04_0435.sL.t = ((21767037274 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0435.sL]
  rw [e0, e1] at h
  exact h

theorem part_054_1 : RS5.BandZeros ((21757413998 : ℝ) / 65536) ((21767037274 : ℝ) / 65536) 254 := by
  have g0 := band_0434
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0435
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((21757413998 : ℝ) / 65536) ((21767037274 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_054_1 <;> assumption
