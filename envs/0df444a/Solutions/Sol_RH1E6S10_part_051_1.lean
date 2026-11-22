-- Prove2me | solution 1 for RH1E6S10.part_051_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T01:14:19.513112+00:00
-- url     : https://prove2.me/submissions/2bcc61d3-7145-43d5-b96c-c24e453d7b2e

import Definitions.Def_RH1E6S10_D051_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0410 : RS5.BandZeros ((41187652501 : ℝ) / 65536) ((41192203644 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0410.s0 RH1E6S10_0410.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0410.s0 RH1E6S10_0410.rest = RH1E6S10_0410.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0410.s0 :: RH1E6S10_0410.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0410.s0.t = ((41187652501 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0410.s0]
  have e1 : RH1E6S10_0410.sL.t = ((41192203644 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0410.sL]
  rw [e0, e1] at h
  exact h

theorem band_0411 : RS5.BandZeros ((41192203644 : ℝ) / 65536) ((41196745802 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0411.s0 RH1E6S10_0411.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0411.s0 RH1E6S10_0411.rest = RH1E6S10_0411.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0411.s0 :: RH1E6S10_0411.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0411.s0.t = ((41192203644 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0411.s0]
  have e1 : RH1E6S10_0411.sL.t = ((41196745802 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0411.sL]
  rw [e0, e1] at h
  exact h

theorem part_051_1 : RS5.BandZeros ((41187652501 : ℝ) / 65536) ((41196745802 : ℝ) / 65536) 254 := by
  have g0 := band_0410
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0411
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41187652501 : ℝ) / 65536) ((41196745802 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_051_1 <;> assumption
