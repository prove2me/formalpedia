-- Prove2me | solution 1 for RH1E6S13.part_083_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T01:53:20.27941+00:00
-- url     : https://prove2.me/submissions/d6ce1996-5ae3-43cf-9594-cea388503971

import Definitions.Def_RH1E6S13_D083_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0668 : RS5.BandZeros ((52132729753 : ℝ) / 65536) ((52137198378 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0668.s0 RH1E6S13_0668.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0668.s0 RH1E6S13_0668.rest = RH1E6S13_0668.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0668.s0 :: RH1E6S13_0668.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0668.s0.t = ((52132729753 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0668.s0]
  have e1 : RH1E6S13_0668.sL.t = ((52137198378 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0668.sL]
  rw [e0, e1] at h
  exact h

theorem band_0669 : RS5.BandZeros ((52137198378 : ℝ) / 65536) ((52141640684 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0669.s0 RH1E6S13_0669.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0669.s0 RH1E6S13_0669.rest = RH1E6S13_0669.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0669.s0 :: RH1E6S13_0669.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0669.s0.t = ((52137198378 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0669.s0]
  have e1 : RH1E6S13_0669.sL.t = ((52141640684 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0669.sL]
  rw [e0, e1] at h
  exact h

theorem part_083_2 : RS5.BandZeros ((52132729753 : ℝ) / 65536) ((52141640684 : ℝ) / 65536) 254 := by
  have g0 := band_0668
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0669
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((52132729753 : ℝ) / 65536) ((52141640684 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_083_2 <;> assumption
