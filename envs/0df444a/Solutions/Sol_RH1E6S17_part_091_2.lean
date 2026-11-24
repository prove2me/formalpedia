-- Prove2me | solution 1 for RH1E6S17.part_091_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:40:43.948796+00:00
-- url     : https://prove2.me/submissions/2890c605-1f1a-41ed-a905-3cc4b3722d75

import Definitions.Def_RH1E6S17_D091_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0732 : RS5.BandZeros ((65462133704 : ℝ) / 65536) ((65466500191 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0732.s0 RH1E6S17_0732.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0732.s0 RH1E6S17_0732.rest = RH1E6S17_0732.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0732.s0 :: RH1E6S17_0732.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0732.s0.t = ((65462133704 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0732.s0]
  have e1 : RH1E6S17_0732.sL.t = ((65466500191 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0732.sL]
  rw [e0, e1] at h
  exact h

theorem band_0733 : RS5.BandZeros ((65466500191 : ℝ) / 65536) ((65470866654 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0733.s0 RH1E6S17_0733.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0733.s0 RH1E6S17_0733.rest = RH1E6S17_0733.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0733.s0 :: RH1E6S17_0733.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0733.s0.t = ((65466500191 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0733.s0]
  have e1 : RH1E6S17_0733.sL.t = ((65470866654 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0733.sL]
  rw [e0, e1] at h
  exact h

theorem part_091_2 : RS5.BandZeros ((65462133704 : ℝ) / 65536) ((65470866654 : ℝ) / 65536) 254 := by
  have g0 := band_0732
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0733
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65462133704 : ℝ) / 65536) ((65470866654 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_091_2 <;> assumption
