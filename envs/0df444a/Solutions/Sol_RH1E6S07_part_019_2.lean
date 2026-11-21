-- Prove2me | solution 1 for RH1E6S07.part_019_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T23:48:38.74994+00:00
-- url     : https://prove2.me/submissions/58a723b0-dd69-4e96-9ace-262cb472f97d

import Definitions.Def_RH1E6S07_D019_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0156 : RS5.BandZeros ((30220168054 : ℝ) / 65536) ((30224809596 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0156.s0 RH1E6S07_0156.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0156.s0 RH1E6S07_0156.rest = RH1E6S07_0156.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0156.s0 :: RH1E6S07_0156.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0156.s0.t = ((30220168054 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0156.s0]
  have e1 : RH1E6S07_0156.sL.t = ((30224809596 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0156.sL]
  rw [e0, e1] at h
  exact h

theorem band_0157 : RS5.BandZeros ((30224809596 : ℝ) / 65536) ((30229490729 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0157.s0 RH1E6S07_0157.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0157.s0 RH1E6S07_0157.rest = RH1E6S07_0157.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0157.s0 :: RH1E6S07_0157.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0157.s0.t = ((30224809596 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0157.s0]
  have e1 : RH1E6S07_0157.sL.t = ((30229490729 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0157.sL]
  rw [e0, e1] at h
  exact h

theorem part_019_2 : RS5.BandZeros ((30220168054 : ℝ) / 65536) ((30229490729 : ℝ) / 65536) 254 := by
  have g0 := band_0156
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0157
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30220168054 : ℝ) / 65536) ((30229490729 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_019_2 <;> assumption
