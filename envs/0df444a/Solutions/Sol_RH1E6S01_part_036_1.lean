-- Prove2me | solution 1 for RH1E6S01.part_036_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:36:19.188729+00:00
-- url     : https://prove2.me/submissions/5ae82058-15d9-4423-8b16-509766e6acfc

import Definitions.Def_RH1E6S01_D036_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0290 : RS5.BandZeros ((11324119669 : ℝ) / 65536) ((11329225467 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0290.s0 RH1E6S01_0290.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0290.s0 RH1E6S01_0290.rest = RH1E6S01_0290.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0290.s0 :: RH1E6S01_0290.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0290.s0.t = ((11324119669 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0290.s0]
  have e1 : RH1E6S01_0290.sL.t = ((11329225467 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0290.sL]
  rw [e0, e1] at h
  exact h

theorem band_0291 : RS5.BandZeros ((11329225467 : ℝ) / 65536) ((11334351180 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0291.s0 RH1E6S01_0291.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0291.s0 RH1E6S01_0291.rest = RH1E6S01_0291.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0291.s0 :: RH1E6S01_0291.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0291.s0.t = ((11329225467 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0291.s0]
  have e1 : RH1E6S01_0291.sL.t = ((11334351180 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0291.sL]
  rw [e0, e1] at h
  exact h

theorem part_036_1 : RS5.BandZeros ((11324119669 : ℝ) / 65536) ((11334351180 : ℝ) / 65536) 254 := by
  have g0 := band_0290
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0291
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11324119669 : ℝ) / 65536) ((11334351180 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_036_1 <;> assumption
