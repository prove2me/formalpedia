-- Prove2me | solution 1 for RH1E6S17.part_091_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:37:28.084933+00:00
-- url     : https://prove2.me/submissions/749e6cec-c245-42f0-a96b-901cb0b22c5c

import Definitions.Def_RH1E6S17_D091_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0728 : RS5.BandZeros ((65444667512 : ℝ) / 65536) ((65449042692 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0728.s0 RH1E6S17_0728.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0728.s0 RH1E6S17_0728.rest = RH1E6S17_0728.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0728.s0 :: RH1E6S17_0728.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0728.s0.t = ((65444667512 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0728.s0]
  have e1 : RH1E6S17_0728.sL.t = ((65449042692 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0728.sL]
  rw [e0, e1] at h
  exact h

theorem band_0729 : RS5.BandZeros ((65449042692 : ℝ) / 65536) ((65453400656 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0729.s0 RH1E6S17_0729.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0729.s0 RH1E6S17_0729.rest = RH1E6S17_0729.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0729.s0 :: RH1E6S17_0729.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0729.s0.t = ((65449042692 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0729.s0]
  have e1 : RH1E6S17_0729.sL.t = ((65453400656 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0729.sL]
  rw [e0, e1] at h
  exact h

theorem part_091_0 : RS5.BandZeros ((65444667512 : ℝ) / 65536) ((65453400656 : ℝ) / 65536) 254 := by
  have g0 := band_0728
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0729
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65444667512 : ℝ) / 65536) ((65453400656 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_091_0 <;> assumption
