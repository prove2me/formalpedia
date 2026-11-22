-- Prove2me | solution 1 for RH1E6S10.part_016_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T18:39:23.091811+00:00
-- url     : https://prove2.me/submissions/d0a4836c-d8cb-431d-a6ac-e41ebdff71d3

import Definitions.Def_RH1E6S10_D016_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0134 : RS5.BandZeros ((39932329006 : ℝ) / 65536) ((39936892416 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0134.s0 RH1E6S10_0134.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0134.s0 RH1E6S10_0134.rest = RH1E6S10_0134.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0134.s0 :: RH1E6S10_0134.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0134.s0.t = ((39932329006 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0134.s0]
  have e1 : RH1E6S10_0134.sL.t = ((39936892416 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0134.sL]
  rw [e0, e1] at h
  exact h

theorem band_0135 : RS5.BandZeros ((39936892416 : ℝ) / 65536) ((39941428886 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0135.s0 RH1E6S10_0135.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0135.s0 RH1E6S10_0135.rest = RH1E6S10_0135.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0135.s0 :: RH1E6S10_0135.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0135.s0.t = ((39936892416 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0135.s0]
  have e1 : RH1E6S10_0135.sL.t = ((39941428886 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0135.sL]
  rw [e0, e1] at h
  exact h

theorem part_016_3 : RS5.BandZeros ((39932329006 : ℝ) / 65536) ((39941428886 : ℝ) / 65536) 254 := by
  have g0 := band_0134
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0135
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39932329006 : ℝ) / 65536) ((39941428886 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_016_3 <;> assumption
