-- Prove2me | solution 1 for RH1E6S02.part_023_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:56:09.602062+00:00
-- url     : https://prove2.me/submissions/bc1c9246-45b7-4296-b970-d3dc47680a79

import Definitions.Def_RH1E6S02_D023_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0184 : RS5.BandZeros ((14032184216 : ℝ) / 65536) ((14037216556 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0184.s0 RH1E6S02_0184.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0184.s0 RH1E6S02_0184.rest = RH1E6S02_0184.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0184.s0 :: RH1E6S02_0184.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0184.s0.t = ((14032184216 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0184.s0]
  have e1 : RH1E6S02_0184.sL.t = ((14037216556 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0184.sL]
  rw [e0, e1] at h
  exact h

theorem band_0185 : RS5.BandZeros ((14037216556 : ℝ) / 65536) ((14042216889 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0185.s0 RH1E6S02_0185.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0185.s0 RH1E6S02_0185.rest = RH1E6S02_0185.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0185.s0 :: RH1E6S02_0185.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0185.s0.t = ((14037216556 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0185.s0]
  have e1 : RH1E6S02_0185.sL.t = ((14042216889 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0185.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_0 : RS5.BandZeros ((14032184216 : ℝ) / 65536) ((14042216889 : ℝ) / 65536) 254 := by
  have g0 := band_0184
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0185
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((14032184216 : ℝ) / 65536) ((14042216889 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_023_0 <;> assumption
