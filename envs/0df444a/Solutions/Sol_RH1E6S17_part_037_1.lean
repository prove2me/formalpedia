-- Prove2me | solution 1 for RH1E6S17.part_037_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T21:41:48.461334+00:00
-- url     : https://prove2.me/submissions/14dba837-7afd-4dfd-b5d0-6613685ae915

import Definitions.Def_RH1E6S17_D037_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0298 : RS5.BandZeros ((63564754581 : ℝ) / 65536) ((63569123201 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0298.s0 RH1E6S17_0298.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0298.s0 RH1E6S17_0298.rest = RH1E6S17_0298.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0298.s0 :: RH1E6S17_0298.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0298.s0.t = ((63564754581 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0298.s0]
  have e1 : RH1E6S17_0298.sL.t = ((63569123201 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0298.sL]
  rw [e0, e1] at h
  exact h

theorem band_0299 : RS5.BandZeros ((63569123201 : ℝ) / 65536) ((63573509029 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0299.s0 RH1E6S17_0299.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0299.s0 RH1E6S17_0299.rest = RH1E6S17_0299.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0299.s0 :: RH1E6S17_0299.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0299.s0.t = ((63569123201 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0299.s0]
  have e1 : RH1E6S17_0299.sL.t = ((63573509029 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0299.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_1 : RS5.BandZeros ((63564754581 : ℝ) / 65536) ((63573509029 : ℝ) / 65536) 254 := by
  have g0 := band_0298
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0299
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63564754581 : ℝ) / 65536) ((63573509029 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_037_1 <;> assumption
