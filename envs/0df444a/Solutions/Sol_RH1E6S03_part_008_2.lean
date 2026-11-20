-- Prove2me | solution 1 for RH1E6S03.part_008_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:33:50.138215+00:00
-- url     : https://prove2.me/submissions/978976ae-68fc-418b-81bc-9a2d04c9dbce

import Definitions.Def_RH1E6S03_D008_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0068 : RS5.BandZeros ((16719436800 : ℝ) / 65536) ((16724355163 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0068.s0 RH1E6S03_0068.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0068.s0 RH1E6S03_0068.rest = RH1E6S03_0068.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0068.s0 :: RH1E6S03_0068.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0068.s0.t = ((16719436800 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0068.s0]
  have e1 : RH1E6S03_0068.sL.t = ((16724355163 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0068.sL]
  rw [e0, e1] at h
  exact h

theorem band_0069 : RS5.BandZeros ((16724355163 : ℝ) / 65536) ((16729273391 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0069.s0 RH1E6S03_0069.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0069.s0 RH1E6S03_0069.rest = RH1E6S03_0069.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0069.s0 :: RH1E6S03_0069.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0069.s0.t = ((16724355163 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0069.s0]
  have e1 : RH1E6S03_0069.sL.t = ((16729273391 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0069.sL]
  rw [e0, e1] at h
  exact h

theorem part_008_2 : RS5.BandZeros ((16719436800 : ℝ) / 65536) ((16729273391 : ℝ) / 65536) 254 := by
  have g0 := band_0068
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0069
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((16719436800 : ℝ) / 65536) ((16729273391 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_008_2 <;> assumption
