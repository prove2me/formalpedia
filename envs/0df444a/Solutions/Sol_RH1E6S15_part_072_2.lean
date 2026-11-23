-- Prove2me | solution 1 for RH1E6S15.part_072_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T12:21:18.254802+00:00
-- url     : https://prove2.me/submissions/5dc8a1f3-9fb5-4b2a-aa19-d99b1feb05fb

import Definitions.Def_RH1E6S15_D072_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0580 : RS5.BandZeros ((58267840540 : ℝ) / 65536) ((58272225370 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0580.s0 RH1E6S15_0580.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0580.s0 RH1E6S15_0580.rest = RH1E6S15_0580.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0580.s0 :: RH1E6S15_0580.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0580.s0.t = ((58267840540 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0580.s0]
  have e1 : RH1E6S15_0580.sL.t = ((58272225370 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0580.sL]
  rw [e0, e1] at h
  exact h

theorem band_0581 : RS5.BandZeros ((58272225370 : ℝ) / 65536) ((58276630992 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0581.s0 RH1E6S15_0581.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0581.s0 RH1E6S15_0581.rest = RH1E6S15_0581.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0581.s0 :: RH1E6S15_0581.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0581.s0.t = ((58272225370 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0581.s0]
  have e1 : RH1E6S15_0581.sL.t = ((58276630992 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0581.sL]
  rw [e0, e1] at h
  exact h

theorem part_072_2 : RS5.BandZeros ((58267840540 : ℝ) / 65536) ((58276630992 : ℝ) / 65536) 254 := by
  have g0 := band_0580
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0581
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58267840540 : ℝ) / 65536) ((58276630992 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_072_2 <;> assumption
