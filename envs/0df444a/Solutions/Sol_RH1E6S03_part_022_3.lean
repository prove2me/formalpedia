-- Prove2me | solution 1 for RH1E6S03.part_022_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:05:42.720676+00:00
-- url     : https://prove2.me/submissions/89b07d9b-2429-4ed2-acd8-3970a4e6aa83

import Definitions.Def_RH1E6S03_D022_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0182 : RS5.BandZeros ((17280357316 : ℝ) / 65536) ((17285270106 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0182.s0 RH1E6S03_0182.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0182.s0 RH1E6S03_0182.rest = RH1E6S03_0182.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0182.s0 :: RH1E6S03_0182.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0182.s0.t = ((17280357316 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0182.s0]
  have e1 : RH1E6S03_0182.sL.t = ((17285270106 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0182.sL]
  rw [e0, e1] at h
  exact h

theorem band_0183 : RS5.BandZeros ((17285270106 : ℝ) / 65536) ((17290182765 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0183.s0 RH1E6S03_0183.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0183.s0 RH1E6S03_0183.rest = RH1E6S03_0183.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0183.s0 :: RH1E6S03_0183.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0183.s0.t = ((17285270106 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0183.s0]
  have e1 : RH1E6S03_0183.sL.t = ((17290182765 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0183.sL]
  rw [e0, e1] at h
  exact h

theorem part_022_3 : RS5.BandZeros ((17280357316 : ℝ) / 65536) ((17290182765 : ℝ) / 65536) 254 := by
  have g0 := band_0182
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0183
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17280357316 : ℝ) / 65536) ((17290182765 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_022_3 <;> assumption
