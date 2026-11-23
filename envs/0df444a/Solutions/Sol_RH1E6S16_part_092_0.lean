-- Prove2me | solution 1 for RH1E6S16.part_092_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:28:11.270371+00:00
-- url     : https://prove2.me/submissions/a9b17231-1e59-45db-a289-e2b9d9dee0ab

import Definitions.Def_RH1E6S16_D092_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0736 : RS5.BandZeros ((62217004170 : ℝ) / 65536) ((62221396843 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0736.s0 RH1E6S16_0736.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0736.s0 RH1E6S16_0736.rest = RH1E6S16_0736.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0736.s0 :: RH1E6S16_0736.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0736.s0.t = ((62217004170 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0736.s0]
  have e1 : RH1E6S16_0736.sL.t = ((62221396843 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0736.sL]
  rw [e0, e1] at h
  exact h

theorem band_0737 : RS5.BandZeros ((62221396843 : ℝ) / 65536) ((62225773287 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0737.s0 RH1E6S16_0737.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0737.s0 RH1E6S16_0737.rest = RH1E6S16_0737.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0737.s0 :: RH1E6S16_0737.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0737.s0.t = ((62221396843 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0737.s0]
  have e1 : RH1E6S16_0737.sL.t = ((62225773287 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0737.sL]
  rw [e0, e1] at h
  exact h

theorem part_092_0 : RS5.BandZeros ((62217004170 : ℝ) / 65536) ((62225773287 : ℝ) / 65536) 254 := by
  have g0 := band_0736
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0737
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((62217004170 : ℝ) / 65536) ((62225773287 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_092_0 <;> assumption
