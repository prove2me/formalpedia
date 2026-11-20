-- Prove2me | solution 1 for RH1E6S03.part_001_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:04:48.223954+00:00
-- url     : https://prove2.me/submissions/1c4357ea-44f8-4127-ac74-76f2aa11c461

import Definitions.Def_RH1E6S03_D001_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0008 : RS5.BandZeros ((16423471394 : ℝ) / 65536) ((16428436916 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0008.s0 RH1E6S03_0008.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0008.s0 RH1E6S03_0008.rest = RH1E6S03_0008.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0008.s0 :: RH1E6S03_0008.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0008.s0.t = ((16423471394 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0008.s0]
  have e1 : RH1E6S03_0008.sL.t = ((16428436916 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0008.sL]
  rw [e0, e1] at h
  exact h

theorem band_0009 : RS5.BandZeros ((16428436916 : ℝ) / 65536) ((16433363430 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0009.s0 RH1E6S03_0009.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0009.s0 RH1E6S03_0009.rest = RH1E6S03_0009.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0009.s0 :: RH1E6S03_0009.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0009.s0.t = ((16428436916 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0009.s0]
  have e1 : RH1E6S03_0009.sL.t = ((16433363430 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0009.sL]
  rw [e0, e1] at h
  exact h

theorem part_001_0 : RS5.BandZeros ((16423471394 : ℝ) / 65536) ((16433363430 : ℝ) / 65536) 254 := by
  have g0 := band_0008
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0009
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((16423471394 : ℝ) / 65536) ((16433363430 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_001_0 <;> assumption
