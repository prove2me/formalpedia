-- Prove2me | solution 1 for RH1E6S14.part_058_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T05:50:01.087124+00:00
-- url     : https://prove2.me/submissions/f1a29fae-bcf6-463b-a555-1ac1f43a8788

import Definitions.Def_RH1E6S14_D058_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0464 : RS5.BandZeros ((54489732584 : ℝ) / 65536) ((54494145042 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0464.s0 RH1E6S14_0464.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0464.s0 RH1E6S14_0464.rest = RH1E6S14_0464.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0464.s0 :: RH1E6S14_0464.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0464.s0.t = ((54489732584 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0464.s0]
  have e1 : RH1E6S14_0464.sL.t = ((54494145042 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0464.sL]
  rw [e0, e1] at h
  exact h

theorem band_0465 : RS5.BandZeros ((54494145042 : ℝ) / 65536) ((54498584140 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0465.s0 RH1E6S14_0465.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0465.s0 RH1E6S14_0465.rest = RH1E6S14_0465.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0465.s0 :: RH1E6S14_0465.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0465.s0.t = ((54494145042 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0465.s0]
  have e1 : RH1E6S14_0465.sL.t = ((54498584140 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0465.sL]
  rw [e0, e1] at h
  exact h

theorem part_058_0 : RS5.BandZeros ((54489732584 : ℝ) / 65536) ((54498584140 : ℝ) / 65536) 254 := by
  have g0 := band_0464
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0465
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((54489732584 : ℝ) / 65536) ((54498584140 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_058_0 <;> assumption
