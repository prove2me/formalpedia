-- Prove2me | solution 1 for RH1E6S16.part_016_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T14:56:19.736549+00:00
-- url     : https://prove2.me/submissions/416b7543-9630-4c78-8599-4a5707226d57

import Definitions.Def_RH1E6S16_D016_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0134 : RS5.BandZeros ((59572396550 : ℝ) / 65536) ((59576800413 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0134.s0 RH1E6S16_0134.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0134.s0 RH1E6S16_0134.rest = RH1E6S16_0134.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0134.s0 :: RH1E6S16_0134.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0134.s0.t = ((59572396550 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0134.s0]
  have e1 : RH1E6S16_0134.sL.t = ((59576800413 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0134.sL]
  rw [e0, e1] at h
  exact h

theorem band_0135 : RS5.BandZeros ((59576800413 : ℝ) / 65536) ((59581196071 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0135.s0 RH1E6S16_0135.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0135.s0 RH1E6S16_0135.rest = RH1E6S16_0135.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0135.s0 :: RH1E6S16_0135.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0135.s0.t = ((59576800413 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0135.s0]
  have e1 : RH1E6S16_0135.sL.t = ((59581196071 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0135.sL]
  rw [e0, e1] at h
  exact h

theorem part_016_3 : RS5.BandZeros ((59572396550 : ℝ) / 65536) ((59581196071 : ℝ) / 65536) 254 := by
  have g0 := band_0134
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0135
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59572396550 : ℝ) / 65536) ((59581196071 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_016_3 <;> assumption
