-- Prove2me | solution 1 for RH1E6S09.part_007_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T08:30:54.576754+00:00
-- url     : https://prove2.me/submissions/cff0724e-43ae-490e-86ed-4c8a79af3e6d

import Definitions.Def_RH1E6S09_D007_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0058 : RS5.BandZeros ((36311230463 : ℝ) / 65536) ((36315820021 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0058.s0 RH1E6S09_0058.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0058.s0 RH1E6S09_0058.rest = RH1E6S09_0058.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0058.s0 :: RH1E6S09_0058.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0058.s0.t = ((36311230463 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0058.s0]
  have e1 : RH1E6S09_0058.sL.t = ((36315820021 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0058.sL]
  rw [e0, e1] at h
  exact h

theorem band_0059 : RS5.BandZeros ((36315820021 : ℝ) / 65536) ((36320403727 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0059.s0 RH1E6S09_0059.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0059.s0 RH1E6S09_0059.rest = RH1E6S09_0059.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0059.s0 :: RH1E6S09_0059.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0059.s0.t = ((36315820021 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0059.s0]
  have e1 : RH1E6S09_0059.sL.t = ((36320403727 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0059.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_1 : RS5.BandZeros ((36311230463 : ℝ) / 65536) ((36320403727 : ℝ) / 65536) 254 := by
  have g0 := band_0058
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0059
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36311230463 : ℝ) / 65536) ((36320403727 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_007_1 <;> assumption
