-- Prove2me | solution 1 for RH1E6S13.part_064_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T00:39:26.663334+00:00
-- url     : https://prove2.me/submissions/a7b56a13-dd10-47da-b41c-7d1ec3d0e81a

import Definitions.Def_RH1E6S13_D064_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0518 : RS5.BandZeros ((51464713868 : ℝ) / 65536) ((51469178631 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0518.s0 RH1E6S13_0518.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0518.s0 RH1E6S13_0518.rest = RH1E6S13_0518.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0518.s0 :: RH1E6S13_0518.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0518.s0.t = ((51464713868 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0518.s0]
  have e1 : RH1E6S13_0518.sL.t = ((51469178631 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0518.sL]
  rw [e0, e1] at h
  exact h

theorem band_0519 : RS5.BandZeros ((51469178631 : ℝ) / 65536) ((51473634590 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0519.s0 RH1E6S13_0519.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0519.s0 RH1E6S13_0519.rest = RH1E6S13_0519.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0519.s0 :: RH1E6S13_0519.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0519.s0.t = ((51469178631 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0519.s0]
  have e1 : RH1E6S13_0519.sL.t = ((51473634590 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0519.sL]
  rw [e0, e1] at h
  exact h

theorem part_064_3 : RS5.BandZeros ((51464713868 : ℝ) / 65536) ((51473634590 : ℝ) / 65536) 254 := by
  have g0 := band_0518
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0519
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51464713868 : ℝ) / 65536) ((51473634590 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_064_3 <;> assumption
