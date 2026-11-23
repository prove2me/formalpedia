-- Prove2me | solution 1 for RH1E6S17.part_005_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:50:11.873859+00:00
-- url     : https://prove2.me/submissions/6523c3fc-c326-4810-899b-39ea62fe60e6

import Definitions.Def_RH1E6S17_D005_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0042 : RS5.BandZeros ((62443345888 : ℝ) / 65536) ((62447746914 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0042.s0 RH1E6S17_0042.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0042.s0 RH1E6S17_0042.rest = RH1E6S17_0042.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0042.s0 :: RH1E6S17_0042.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0042.s0.t = ((62443345888 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0042.s0]
  have e1 : RH1E6S17_0042.sL.t = ((62447746914 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0042.sL]
  rw [e0, e1] at h
  exact h

theorem band_0043 : RS5.BandZeros ((62447746914 : ℝ) / 65536) ((62452104768 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0043.s0 RH1E6S17_0043.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0043.s0 RH1E6S17_0043.rest = RH1E6S17_0043.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0043.s0 :: RH1E6S17_0043.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0043.s0.t = ((62447746914 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0043.s0]
  have e1 : RH1E6S17_0043.sL.t = ((62452104768 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0043.sL]
  rw [e0, e1] at h
  exact h

theorem part_005_1 : RS5.BandZeros ((62443345888 : ℝ) / 65536) ((62452104768 : ℝ) / 65536) 254 := by
  have g0 := band_0042
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0043
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((62443345888 : ℝ) / 65536) ((62452104768 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_005_1 <;> assumption
