-- Prove2me | solution 1 for RH1E6S08.part_081_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T07:50:24.559358+00:00
-- url     : https://prove2.me/submissions/484ddaa6-c951-409f-ab50-0fef5d4558ba

import Definitions.Def_RH1E6S08_D081_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0654 : RS5.BandZeros ((35786879706 : ℝ) / 65536) ((35791485999 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0654.s0 RH1E6S08_0654.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0654.s0 RH1E6S08_0654.rest = RH1E6S08_0654.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0654.s0 :: RH1E6S08_0654.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0654.s0.t = ((35786879706 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0654.s0]
  have e1 : RH1E6S08_0654.sL.t = ((35791485999 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0654.sL]
  rw [e0, e1] at h
  exact h

theorem band_0655 : RS5.BandZeros ((35791485999 : ℝ) / 65536) ((35796085378 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0655.s0 RH1E6S08_0655.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0655.s0 RH1E6S08_0655.rest = RH1E6S08_0655.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0655.s0 :: RH1E6S08_0655.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0655.s0.t = ((35791485999 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0655.s0]
  have e1 : RH1E6S08_0655.sL.t = ((35796085378 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0655.sL]
  rw [e0, e1] at h
  exact h

theorem part_081_3 : RS5.BandZeros ((35786879706 : ℝ) / 65536) ((35796085378 : ℝ) / 65536) 254 := by
  have g0 := band_0654
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0655
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35786879706 : ℝ) / 65536) ((35796085378 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_081_3 <;> assumption
