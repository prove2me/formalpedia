-- Prove2me | solution 1 for RH1E6S13.part_066_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T00:44:58.867819+00:00
-- url     : https://prove2.me/submissions/71b398b6-8a27-4d97-b509-a826d35ef7f3

import Definitions.Def_RH1E6S13_D066_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0528 : RS5.BandZeros ((51509272308 : ℝ) / 65536) ((51513727972 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0528.s0 RH1E6S13_0528.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0528.s0 RH1E6S13_0528.rest = RH1E6S13_0528.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0528.s0 :: RH1E6S13_0528.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0528.s0.t = ((51509272308 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0528.s0]
  have e1 : RH1E6S13_0528.sL.t = ((51513727972 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0528.sL]
  rw [e0, e1] at h
  exact h

theorem band_0529 : RS5.BandZeros ((51513727972 : ℝ) / 65536) ((51518183602 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0529.s0 RH1E6S13_0529.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0529.s0 RH1E6S13_0529.rest = RH1E6S13_0529.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0529.s0 :: RH1E6S13_0529.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0529.s0.t = ((51513727972 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0529.s0]
  have e1 : RH1E6S13_0529.sL.t = ((51518183602 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0529.sL]
  rw [e0, e1] at h
  exact h

theorem part_066_0 : RS5.BandZeros ((51509272308 : ℝ) / 65536) ((51518183602 : ℝ) / 65536) 254 := by
  have g0 := band_0528
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0529
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51509272308 : ℝ) / 65536) ((51518183602 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_066_0 <;> assumption
