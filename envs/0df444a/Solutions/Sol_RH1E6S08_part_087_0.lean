-- Prove2me | solution 1 for RH1E6S08.part_087_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T08:03:49.087102+00:00
-- url     : https://prove2.me/submissions/54c738b8-6e9d-4b15-b3d3-6f472e4efc70

import Definitions.Def_RH1E6S08_D087_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0696 : RS5.BandZeros ((35979968488 : ℝ) / 65536) ((35984571024 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0696.s0 RH1E6S08_0696.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0696.s0 RH1E6S08_0696.rest = RH1E6S08_0696.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0696.s0 :: RH1E6S08_0696.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0696.s0.t = ((35979968488 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0696.s0]
  have e1 : RH1E6S08_0696.sL.t = ((35984571024 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0696.sL]
  rw [e0, e1] at h
  exact h

theorem band_0697 : RS5.BandZeros ((35984571024 : ℝ) / 65536) ((35989160012 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0697.s0 RH1E6S08_0697.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0697.s0 RH1E6S08_0697.rest = RH1E6S08_0697.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0697.s0 :: RH1E6S08_0697.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0697.s0.t = ((35984571024 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0697.s0]
  have e1 : RH1E6S08_0697.sL.t = ((35989160012 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0697.sL]
  rw [e0, e1] at h
  exact h

theorem part_087_0 : RS5.BandZeros ((35979968488 : ℝ) / 65536) ((35989160012 : ℝ) / 65536) 254 := by
  have g0 := band_0696
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0697
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35979968488 : ℝ) / 65536) ((35989160012 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_087_0 <;> assumption
