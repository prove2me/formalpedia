-- Prove2me | solution 1 for RH1E6S07.part_014_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T23:34:44.907375+00:00
-- url     : https://prove2.me/submissions/d323a344-3fe7-4fc8-84dc-b97519826103

import Definitions.Def_RH1E6S07_D014_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0112 : RS5.BandZeros ((30014724330 : ℝ) / 65536) ((30019393670 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0112.s0 RH1E6S07_0112.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0112.s0 RH1E6S07_0112.rest = RH1E6S07_0112.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0112.s0 :: RH1E6S07_0112.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0112.s0.t = ((30014724330 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0112.s0]
  have e1 : RH1E6S07_0112.sL.t = ((30019393670 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0112.sL]
  rw [e0, e1] at h
  exact h

theorem band_0113 : RS5.BandZeros ((30019393670 : ℝ) / 65536) ((30024054117 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0113.s0 RH1E6S07_0113.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0113.s0 RH1E6S07_0113.rest = RH1E6S07_0113.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0113.s0 :: RH1E6S07_0113.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0113.s0.t = ((30019393670 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0113.s0]
  have e1 : RH1E6S07_0113.sL.t = ((30024054117 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0113.sL]
  rw [e0, e1] at h
  exact h

theorem part_014_0 : RS5.BandZeros ((30014724330 : ℝ) / 65536) ((30024054117 : ℝ) / 65536) 254 := by
  have g0 := band_0112
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0113
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30014724330 : ℝ) / 65536) ((30024054117 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_014_0 <;> assumption
