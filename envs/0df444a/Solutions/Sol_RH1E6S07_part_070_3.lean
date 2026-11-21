-- Prove2me | solution 1 for RH1E6S07.part_070_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T02:15:58.797425+00:00
-- url     : https://prove2.me/submissions/92418ec2-ae12-402a-8237-eccb50b30587

import Definitions.Def_RH1E6S07_D070_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0566 : RS5.BandZeros ((32128676919 : ℝ) / 65536) ((32133311832 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0566.s0 RH1E6S07_0566.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0566.s0 RH1E6S07_0566.rest = RH1E6S07_0566.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0566.s0 :: RH1E6S07_0566.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0566.s0.t = ((32128676919 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0566.s0]
  have e1 : RH1E6S07_0566.sL.t = ((32133311832 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0566.sL]
  rw [e0, e1] at h
  exact h

theorem band_0567 : RS5.BandZeros ((32133311832 : ℝ) / 65536) ((32137954123 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0567.s0 RH1E6S07_0567.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0567.s0 RH1E6S07_0567.rest = RH1E6S07_0567.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0567.s0 :: RH1E6S07_0567.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0567.s0.t = ((32133311832 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0567.s0]
  have e1 : RH1E6S07_0567.sL.t = ((32137954123 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0567.sL]
  rw [e0, e1] at h
  exact h

theorem part_070_3 : RS5.BandZeros ((32128676919 : ℝ) / 65536) ((32137954123 : ℝ) / 65536) 254 := by
  have g0 := band_0566
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0567
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((32128676919 : ℝ) / 65536) ((32137954123 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_070_3 <;> assumption
