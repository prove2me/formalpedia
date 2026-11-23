-- Prove2me | solution 1 for RH1E6S14.part_090_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:40:11.86114+00:00
-- url     : https://prove2.me/submissions/75947de3-e244-45ec-8b4f-ac090456b029

import Definitions.Def_RH1E6S14_D090_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0722 : RS5.BandZeros ((55632783236 : ℝ) / 65536) ((55637220839 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0722.s0 RH1E6S14_0722.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0722.s0 RH1E6S14_0722.rest = RH1E6S14_0722.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0722.s0 :: RH1E6S14_0722.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0722.s0.t = ((55632783236 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0722.s0]
  have e1 : RH1E6S14_0722.sL.t = ((55637220839 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0722.sL]
  rw [e0, e1] at h
  exact h

theorem band_0723 : RS5.BandZeros ((55637220839 : ℝ) / 65536) ((55641645031 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0723.s0 RH1E6S14_0723.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0723.s0 RH1E6S14_0723.rest = RH1E6S14_0723.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0723.s0 :: RH1E6S14_0723.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0723.s0.t = ((55637220839 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0723.s0]
  have e1 : RH1E6S14_0723.sL.t = ((55641645031 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0723.sL]
  rw [e0, e1] at h
  exact h

theorem part_090_1 : RS5.BandZeros ((55632783236 : ℝ) / 65536) ((55641645031 : ℝ) / 65536) 254 := by
  have g0 := band_0722
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0723
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55632783236 : ℝ) / 65536) ((55641645031 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_090_1 <;> assumption
