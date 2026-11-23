-- Prove2me | solution 1 for RH1E6S14.part_090_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:40:15.8928+00:00
-- url     : https://prove2.me/submissions/963c4b27-f083-4460-86c6-9f50683052f0

import Definitions.Def_RH1E6S14_D090_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0726 : RS5.BandZeros ((55650504268 : ℝ) / 65536) ((55654919163 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0726.s0 RH1E6S14_0726.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0726.s0 RH1E6S14_0726.rest = RH1E6S14_0726.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0726.s0 :: RH1E6S14_0726.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0726.s0.t = ((55650504268 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0726.s0]
  have e1 : RH1E6S14_0726.sL.t = ((55654919163 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0726.sL]
  rw [e0, e1] at h
  exact h

theorem band_0727 : RS5.BandZeros ((55654919163 : ℝ) / 65536) ((55659343584 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0727.s0 RH1E6S14_0727.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0727.s0 RH1E6S14_0727.rest = RH1E6S14_0727.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0727.s0 :: RH1E6S14_0727.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0727.s0.t = ((55654919163 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0727.s0]
  have e1 : RH1E6S14_0727.sL.t = ((55659343584 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0727.sL]
  rw [e0, e1] at h
  exact h

theorem part_090_3 : RS5.BandZeros ((55650504268 : ℝ) / 65536) ((55659343584 : ℝ) / 65536) 254 := by
  have g0 := band_0726
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0727
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55650504268 : ℝ) / 65536) ((55659343584 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_090_3 <;> assumption
