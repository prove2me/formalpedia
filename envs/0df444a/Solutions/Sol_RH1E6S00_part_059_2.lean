-- Prove2me | solution 1 for RH1E6S00.part_059_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T22:47:43.151228+00:00
-- url     : https://prove2.me/submissions/7ef00d01-7f2d-4517-9df4-c9d2b6798091

import Definitions.Def_RH1E6S00_D059_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0476 : RS5.BandZeros ((9081552801 : ℝ) / 65536) ((9086781522 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0476.s0 RH1E6S00_0476.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0476.s0 RH1E6S00_0476.rest = RH1E6S00_0476.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0476.s0 :: RH1E6S00_0476.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0476.s0.t = ((9081552801 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0476.s0]
  have e1 : RH1E6S00_0476.sL.t = ((9086781522 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0476.sL]
  rw [e0, e1] at h
  exact h

theorem band_0477 : RS5.BandZeros ((9086781522 : ℝ) / 65536) ((9092009942 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0477.s0 RH1E6S00_0477.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0477.s0 RH1E6S00_0477.rest = RH1E6S00_0477.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0477.s0 :: RH1E6S00_0477.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0477.s0.t = ((9086781522 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0477.s0]
  have e1 : RH1E6S00_0477.sL.t = ((9092009942 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0477.sL]
  rw [e0, e1] at h
  exact h

theorem part_059_2 : RS5.BandZeros ((9081552801 : ℝ) / 65536) ((9092009942 : ℝ) / 65536) 254 := by
  have g0 := band_0476
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0477
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9081552801 : ℝ) / 65536) ((9092009942 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_059_2 <;> assumption
