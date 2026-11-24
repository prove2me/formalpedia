-- Prove2me | solution 1 for RH1E6S17.part_078_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T23:59:09.128859+00:00
-- url     : https://prove2.me/submissions/625b6cce-40dc-4af8-8f3f-8a551de15869

import Definitions.Def_RH1E6S17_D078_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0630 : RS5.BandZeros ((65016615309 : ℝ) / 65536) ((65020992887 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0630.s0 RH1E6S17_0630.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0630.s0 RH1E6S17_0630.rest = RH1E6S17_0630.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0630.s0 :: RH1E6S17_0630.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0630.s0.t = ((65016615309 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0630.s0]
  have e1 : RH1E6S17_0630.sL.t = ((65020992887 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0630.sL]
  rw [e0, e1] at h
  exact h

theorem band_0631 : RS5.BandZeros ((65020992887 : ℝ) / 65536) ((65025379042 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0631.s0 RH1E6S17_0631.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0631.s0 RH1E6S17_0631.rest = RH1E6S17_0631.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0631.s0 :: RH1E6S17_0631.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0631.s0.t = ((65020992887 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0631.s0]
  have e1 : RH1E6S17_0631.sL.t = ((65025379042 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0631.sL]
  rw [e0, e1] at h
  exact h

theorem part_078_3 : RS5.BandZeros ((65016615309 : ℝ) / 65536) ((65025379042 : ℝ) / 65536) 254 := by
  have g0 := band_0630
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0631
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65016615309 : ℝ) / 65536) ((65025379042 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_078_3 <;> assumption
