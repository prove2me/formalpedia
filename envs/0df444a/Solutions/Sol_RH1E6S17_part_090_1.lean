-- Prove2me | solution 1 for RH1E6S17.part_090_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:37:22.058157+00:00
-- url     : https://prove2.me/submissions/53314b5f-fd7e-4d23-bbee-78ffaee3840d

import Definitions.Def_RH1E6S17_D090_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0722 : RS5.BandZeros ((65418458899 : ℝ) / 65536) ((65422834225 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0722.s0 RH1E6S17_0722.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0722.s0 RH1E6S17_0722.rest = RH1E6S17_0722.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0722.s0 :: RH1E6S17_0722.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0722.s0.t = ((65418458899 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0722.s0]
  have e1 : RH1E6S17_0722.sL.t = ((65422834225 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0722.sL]
  rw [e0, e1] at h
  exact h

theorem band_0723 : RS5.BandZeros ((65422834225 : ℝ) / 65536) ((65427200931 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0723.s0 RH1E6S17_0723.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0723.s0 RH1E6S17_0723.rest = RH1E6S17_0723.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0723.s0 :: RH1E6S17_0723.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0723.s0.t = ((65422834225 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0723.s0]
  have e1 : RH1E6S17_0723.sL.t = ((65427200931 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0723.sL]
  rw [e0, e1] at h
  exact h

theorem part_090_1 : RS5.BandZeros ((65418458899 : ℝ) / 65536) ((65427200931 : ℝ) / 65536) 254 := by
  have g0 := band_0722
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0723
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65418458899 : ℝ) / 65536) ((65427200931 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_090_1 <;> assumption
