-- Prove2me | solution 1 for RH1E6S03.part_010_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:38:42.864556+00:00
-- url     : https://prove2.me/submissions/e352ca42-608c-4b00-9276-41a60772235f

import Definitions.Def_RH1E6S03_D010_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0082 : RS5.BandZeros ((16788426966 : ℝ) / 65536) ((16793333725 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0082.s0 RH1E6S03_0082.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0082.s0 RH1E6S03_0082.rest = RH1E6S03_0082.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0082.s0 :: RH1E6S03_0082.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0082.s0.t = ((16788426966 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0082.s0]
  have e1 : RH1E6S03_0082.sL.t = ((16793333725 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0082.sL]
  rw [e0, e1] at h
  exact h

theorem band_0083 : RS5.BandZeros ((16793333725 : ℝ) / 65536) ((16798250046 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0083.s0 RH1E6S03_0083.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0083.s0 RH1E6S03_0083.rest = RH1E6S03_0083.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0083.s0 :: RH1E6S03_0083.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0083.s0.t = ((16793333725 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0083.s0]
  have e1 : RH1E6S03_0083.sL.t = ((16798250046 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0083.sL]
  rw [e0, e1] at h
  exact h

theorem part_010_1 : RS5.BandZeros ((16788426966 : ℝ) / 65536) ((16798250046 : ℝ) / 65536) 254 := by
  have g0 := band_0082
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0083
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((16788426966 : ℝ) / 65536) ((16798250046 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_010_1 <;> assumption
