-- Prove2me | solution 1 for RH1E6S03.part_081_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T08:18:36.760808+00:00
-- url     : https://prove2.me/submissions/ecf97f7c-aaa4-4d18-9828-0e2d05de41e7

import Definitions.Def_RH1E6S03_D081_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0654 : RS5.BandZeros ((19585385202 : ℝ) / 65536) ((19590240883 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0654.s0 RH1E6S03_0654.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0654.s0 RH1E6S03_0654.rest = RH1E6S03_0654.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0654.s0 :: RH1E6S03_0654.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0654.s0.t = ((19585385202 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0654.s0]
  have e1 : RH1E6S03_0654.sL.t = ((19590240883 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0654.sL]
  rw [e0, e1] at h
  exact h

theorem band_0655 : RS5.BandZeros ((19590240883 : ℝ) / 65536) ((19595086895 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0655.s0 RH1E6S03_0655.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0655.s0 RH1E6S03_0655.rest = RH1E6S03_0655.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0655.s0 :: RH1E6S03_0655.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0655.s0.t = ((19590240883 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0655.s0]
  have e1 : RH1E6S03_0655.sL.t = ((19595086895 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0655.sL]
  rw [e0, e1] at h
  exact h

theorem part_081_3 : RS5.BandZeros ((19585385202 : ℝ) / 65536) ((19595086895 : ℝ) / 65536) 254 := by
  have g0 := band_0654
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0655
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((19585385202 : ℝ) / 65536) ((19595086895 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_081_3 <;> assumption
