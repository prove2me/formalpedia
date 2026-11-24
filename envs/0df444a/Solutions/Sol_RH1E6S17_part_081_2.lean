-- Prove2me | solution 1 for RH1E6S17.part_081_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:08:36.011583+00:00
-- url     : https://prove2.me/submissions/1ba67db7-73e6-42b3-8aea-80292aabc0c1

import Definitions.Def_RH1E6S17_D081_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0652 : RS5.BandZeros ((65112744366 : ℝ) / 65536) ((65117095607 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0652.s0 RH1E6S17_0652.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0652.s0 RH1E6S17_0652.rest = RH1E6S17_0652.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0652.s0 :: RH1E6S17_0652.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0652.s0.t = ((65112744366 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0652.s0]
  have e1 : RH1E6S17_0652.sL.t = ((65117095607 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0652.sL]
  rw [e0, e1] at h
  exact h

theorem band_0653 : RS5.BandZeros ((65117095607 : ℝ) / 65536) ((65121472620 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0653.s0 RH1E6S17_0653.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0653.s0 RH1E6S17_0653.rest = RH1E6S17_0653.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0653.s0 :: RH1E6S17_0653.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0653.s0.t = ((65117095607 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0653.s0]
  have e1 : RH1E6S17_0653.sL.t = ((65121472620 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0653.sL]
  rw [e0, e1] at h
  exact h

theorem part_081_2 : RS5.BandZeros ((65112744366 : ℝ) / 65536) ((65121472620 : ℝ) / 65536) 254 := by
  have g0 := band_0652
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0653
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65112744366 : ℝ) / 65536) ((65121472620 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_081_2 <;> assumption
