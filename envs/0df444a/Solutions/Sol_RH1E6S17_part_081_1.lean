-- Prove2me | solution 1 for RH1E6S17.part_081_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:08:34.023212+00:00
-- url     : https://prove2.me/submissions/8c290505-7b49-4bac-a2af-8fda66281709

import Definitions.Def_RH1E6S17_D081_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0650 : RS5.BandZeros ((65103998815 : ℝ) / 65536) ((65108358704 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0650.s0 RH1E6S17_0650.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0650.s0 RH1E6S17_0650.rest = RH1E6S17_0650.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0650.s0 :: RH1E6S17_0650.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0650.s0.t = ((65103998815 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0650.s0]
  have e1 : RH1E6S17_0650.sL.t = ((65108358704 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0650.sL]
  rw [e0, e1] at h
  exact h

theorem band_0651 : RS5.BandZeros ((65108358704 : ℝ) / 65536) ((65112744366 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0651.s0 RH1E6S17_0651.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0651.s0 RH1E6S17_0651.rest = RH1E6S17_0651.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0651.s0 :: RH1E6S17_0651.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0651.s0.t = ((65108358704 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0651.s0]
  have e1 : RH1E6S17_0651.sL.t = ((65112744366 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0651.sL]
  rw [e0, e1] at h
  exact h

theorem part_081_1 : RS5.BandZeros ((65103998815 : ℝ) / 65536) ((65112744366 : ℝ) / 65536) 254 := by
  have g0 := band_0650
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0651
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65103998815 : ℝ) / 65536) ((65112744366 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_081_1 <;> assumption
