-- Prove2me | solution 1 for RH1E6S07.part_052_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:25:09.496025+00:00
-- url     : https://prove2.me/submissions/faac7f5f-dd52-40b2-8493-5f0d514bb058

import Definitions.Def_RH1E6S07_D052_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0420 : RS5.BandZeros ((31450237930 : ℝ) / 65536) ((31454890407 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0420.s0 RH1E6S07_0420.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0420.s0 RH1E6S07_0420.rest = RH1E6S07_0420.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0420.s0 :: RH1E6S07_0420.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0420.s0.t = ((31450237930 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0420.s0]
  have e1 : RH1E6S07_0420.sL.t = ((31454890407 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0420.sL]
  rw [e0, e1] at h
  exact h

theorem band_0421 : RS5.BandZeros ((31454890407 : ℝ) / 65536) ((31459537945 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0421.s0 RH1E6S07_0421.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0421.s0 RH1E6S07_0421.rest = RH1E6S07_0421.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0421.s0 :: RH1E6S07_0421.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0421.s0.t = ((31454890407 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0421.s0]
  have e1 : RH1E6S07_0421.sL.t = ((31459537945 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0421.sL]
  rw [e0, e1] at h
  exact h

theorem part_052_2 : RS5.BandZeros ((31450237930 : ℝ) / 65536) ((31459537945 : ℝ) / 65536) 254 := by
  have g0 := band_0420
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0421
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31450237930 : ℝ) / 65536) ((31459537945 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_052_2 <;> assumption
