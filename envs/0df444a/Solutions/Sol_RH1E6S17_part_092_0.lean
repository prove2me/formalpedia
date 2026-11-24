-- Prove2me | solution 1 for RH1E6S17.part_092_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:40:47.927891+00:00
-- url     : https://prove2.me/submissions/cdc40391-5d17-4994-93be-58a67760e91b

import Definitions.Def_RH1E6S17_D092_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0736 : RS5.BandZeros ((65479582316 : ℝ) / 65536) ((65483974491 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0736.s0 RH1E6S17_0736.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0736.s0 RH1E6S17_0736.rest = RH1E6S17_0736.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0736.s0 :: RH1E6S17_0736.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0736.s0.t = ((65479582316 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0736.s0]
  have e1 : RH1E6S17_0736.sL.t = ((65483974491 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0736.sL]
  rw [e0, e1] at h
  exact h

theorem band_0737 : RS5.BandZeros ((65483974491 : ℝ) / 65536) ((65488332262 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0737.s0 RH1E6S17_0737.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0737.s0 RH1E6S17_0737.rest = RH1E6S17_0737.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0737.s0 :: RH1E6S17_0737.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0737.s0.t = ((65483974491 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0737.s0]
  have e1 : RH1E6S17_0737.sL.t = ((65488332262 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0737.sL]
  rw [e0, e1] at h
  exact h

theorem part_092_0 : RS5.BandZeros ((65479582316 : ℝ) / 65536) ((65488332262 : ℝ) / 65536) 254 := by
  have g0 := band_0736
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0737
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65479582316 : ℝ) / 65536) ((65488332262 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_092_0 <;> assumption
