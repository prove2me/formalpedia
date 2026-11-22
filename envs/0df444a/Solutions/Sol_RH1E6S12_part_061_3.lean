-- Prove2me | solution 1 for RH1E6S12.part_061_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T10:23:02.632801+00:00
-- url     : https://prove2.me/submissions/5c079484-aace-4573-b375-1f54d73c1cbe

import Definitions.Def_RH1E6S12_D061_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0494 : RS5.BandZeros ((48093711351 : ℝ) / 65536) ((48098200779 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0494.s0 RH1E6S12_0494.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0494.s0 RH1E6S12_0494.rest = RH1E6S12_0494.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0494.s0 :: RH1E6S12_0494.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0494.s0.t = ((48093711351 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0494.s0]
  have e1 : RH1E6S12_0494.sL.t = ((48098200779 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0494.sL]
  rw [e0, e1] at h
  exact h

theorem band_0495 : RS5.BandZeros ((48098200779 : ℝ) / 65536) ((48102692684 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0495.s0 RH1E6S12_0495.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0495.s0 RH1E6S12_0495.rest = RH1E6S12_0495.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0495.s0 :: RH1E6S12_0495.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0495.s0.t = ((48098200779 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0495.s0]
  have e1 : RH1E6S12_0495.sL.t = ((48102692684 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0495.sL]
  rw [e0, e1] at h
  exact h

theorem part_061_3 : RS5.BandZeros ((48093711351 : ℝ) / 65536) ((48102692684 : ℝ) / 65536) 254 := by
  have g0 := band_0494
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0495
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48093711351 : ℝ) / 65536) ((48102692684 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_061_3 <;> assumption
