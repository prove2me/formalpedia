-- Prove2me | solution 1 for RH1E6S03.part_010_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:38:46.875058+00:00
-- url     : https://prove2.me/submissions/55b5ec7f-7eda-4c9d-93b4-17d0eddd0f18

import Definitions.Def_RH1E6S03_D010_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0086 : RS5.BandZeros ((16808111370 : ℝ) / 65536) ((16813036980 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0086.s0 RH1E6S03_0086.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0086.s0 RH1E6S03_0086.rest = RH1E6S03_0086.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0086.s0 :: RH1E6S03_0086.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0086.s0.t = ((16808111370 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0086.s0]
  have e1 : RH1E6S03_0086.sL.t = ((16813036980 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0086.sL]
  rw [e0, e1] at h
  exact h

theorem band_0087 : RS5.BandZeros ((16813036980 : ℝ) / 65536) ((16817962453 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0087.s0 RH1E6S03_0087.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0087.s0 RH1E6S03_0087.rest = RH1E6S03_0087.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0087.s0 :: RH1E6S03_0087.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0087.s0.t = ((16813036980 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0087.s0]
  have e1 : RH1E6S03_0087.sL.t = ((16817962453 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0087.sL]
  rw [e0, e1] at h
  exact h

theorem part_010_3 : RS5.BandZeros ((16808111370 : ℝ) / 65536) ((16817962453 : ℝ) / 65536) 254 := by
  have g0 := band_0086
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0087
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((16808111370 : ℝ) / 65536) ((16817962453 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_010_3 <;> assumption
