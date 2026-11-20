-- Prove2me | solution 1 for RH1E6S03.part_004_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:26:33.437821+00:00
-- url     : https://prove2.me/submissions/c3f8ea83-0907-41e8-9926-379806f3cedb

import Definitions.Def_RH1E6S03_D004_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0038 : RS5.BandZeros ((16571530979 : ℝ) / 65536) ((16576443755 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0038.s0 RH1E6S03_0038.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0038.s0 RH1E6S03_0038.rest = RH1E6S03_0038.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0038.s0 :: RH1E6S03_0038.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0038.s0.t = ((16571530979 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0038.s0]
  have e1 : RH1E6S03_0038.sL.t = ((16576443755 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0038.sL]
  rw [e0, e1] at h
  exact h

theorem band_0039 : RS5.BandZeros ((16576443755 : ℝ) / 65536) ((16581375811 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0039.s0 RH1E6S03_0039.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0039.s0 RH1E6S03_0039.rest = RH1E6S03_0039.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0039.s0 :: RH1E6S03_0039.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0039.s0.t = ((16576443755 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0039.s0]
  have e1 : RH1E6S03_0039.sL.t = ((16581375811 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0039.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_3 : RS5.BandZeros ((16571530979 : ℝ) / 65536) ((16581375811 : ℝ) / 65536) 254 := by
  have g0 := band_0038
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0039
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((16571530979 : ℝ) / 65536) ((16581375811 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_004_3 <;> assumption
