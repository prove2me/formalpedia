-- Prove2me | solution 1 for RH1E6S16.part_087_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:15:35.586265+00:00
-- url     : https://prove2.me/submissions/3a44f0bc-9b94-4f19-b1f1-1f60d380d003

import Definitions.Def_RH1E6S16_D087_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0702 : RS5.BandZeros ((62067887020 : ℝ) / 65536) ((62072288813 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0702.s0 RH1E6S16_0702.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0702.s0 RH1E6S16_0702.rest = RH1E6S16_0702.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0702.s0 :: RH1E6S16_0702.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0702.s0.t = ((62067887020 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0702.s0]
  have e1 : RH1E6S16_0702.sL.t = ((62072288813 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0702.sL]
  rw [e0, e1] at h
  exact h

theorem band_0703 : RS5.BandZeros ((62072288813 : ℝ) / 65536) ((62076680755 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0703.s0 RH1E6S16_0703.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0703.s0 RH1E6S16_0703.rest = RH1E6S16_0703.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0703.s0 :: RH1E6S16_0703.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0703.s0.t = ((62072288813 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0703.s0]
  have e1 : RH1E6S16_0703.sL.t = ((62076680755 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0703.sL]
  rw [e0, e1] at h
  exact h

theorem part_087_3 : RS5.BandZeros ((62067887020 : ℝ) / 65536) ((62076680755 : ℝ) / 65536) 254 := by
  have g0 := band_0702
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0703
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((62067887020 : ℝ) / 65536) ((62076680755 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_087_3 <;> assumption
