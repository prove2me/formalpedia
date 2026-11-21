-- Prove2me | solution 1 for RH1E6S07.part_061_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:48:48.60538+00:00
-- url     : https://prove2.me/submissions/cbc1e1ae-efc1-4e86-831d-3ae862cc6ded

import Definitions.Def_RH1E6S07_D061_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0494 : RS5.BandZeros ((31794253932 : ℝ) / 65536) ((31798918892 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0494.s0 RH1E6S07_0494.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0494.s0 RH1E6S07_0494.rest = RH1E6S07_0494.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0494.s0 :: RH1E6S07_0494.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0494.s0.t = ((31794253932 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0494.s0]
  have e1 : RH1E6S07_0494.sL.t = ((31798918892 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0494.sL]
  rw [e0, e1] at h
  exact h

theorem band_0495 : RS5.BandZeros ((31798918892 : ℝ) / 65536) ((31803555967 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0495.s0 RH1E6S07_0495.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0495.s0 RH1E6S07_0495.rest = RH1E6S07_0495.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0495.s0 :: RH1E6S07_0495.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0495.s0.t = ((31798918892 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0495.s0]
  have e1 : RH1E6S07_0495.sL.t = ((31803555967 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0495.sL]
  rw [e0, e1] at h
  exact h

theorem part_061_3 : RS5.BandZeros ((31794253932 : ℝ) / 65536) ((31803555967 : ℝ) / 65536) 254 := by
  have g0 := band_0494
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0495
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31794253932 : ℝ) / 65536) ((31803555967 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_061_3 <;> assumption
