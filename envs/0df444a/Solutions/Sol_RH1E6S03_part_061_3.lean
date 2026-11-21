-- Prove2me | solution 1 for RH1E6S03.part_061_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T07:31:45.627722+00:00
-- url     : https://prove2.me/submissions/940df7ef-936d-428a-810f-3b2d5569ce2b

import Definitions.Def_RH1E6S03_D061_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0494 : RS5.BandZeros ((18807011665 : ℝ) / 65536) ((18811885697 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0494.s0 RH1E6S03_0494.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0494.s0 RH1E6S03_0494.rest = RH1E6S03_0494.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0494.s0 :: RH1E6S03_0494.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0494.s0.t = ((18807011665 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0494.s0]
  have e1 : RH1E6S03_0494.sL.t = ((18811885697 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0494.sL]
  rw [e0, e1] at h
  exact h

theorem band_0495 : RS5.BandZeros ((18811885697 : ℝ) / 65536) ((18816750017 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0495.s0 RH1E6S03_0495.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0495.s0 RH1E6S03_0495.rest = RH1E6S03_0495.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0495.s0 :: RH1E6S03_0495.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0495.s0.t = ((18811885697 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0495.s0]
  have e1 : RH1E6S03_0495.sL.t = ((18816750017 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0495.sL]
  rw [e0, e1] at h
  exact h

theorem part_061_3 : RS5.BandZeros ((18807011665 : ℝ) / 65536) ((18816750017 : ℝ) / 65536) 254 := by
  have g0 := band_0494
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0495
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18807011665 : ℝ) / 65536) ((18816750017 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_061_3 <;> assumption
