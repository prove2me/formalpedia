-- Prove2me | solution 1 for RH1E6S05.part_084_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:10:04.965707+00:00
-- url     : https://prove2.me/submissions/37f1f011-cf45-401b-a313-9c6eb8a72c97

import Definitions.Def_RH1E6S05_D084_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0678 : RS5.BandZeros ((26162349033 : ℝ) / 65536) ((26167086915 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0678.s0 RH1E6S05_0678.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0678.s0 RH1E6S05_0678.rest = RH1E6S05_0678.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0678.s0 :: RH1E6S05_0678.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0678.s0.t = ((26162349033 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0678.s0]
  have e1 : RH1E6S05_0678.sL.t = ((26167086915 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0678.sL]
  rw [e0, e1] at h
  exact h

theorem band_0679 : RS5.BandZeros ((26167086915 : ℝ) / 65536) ((26171824719 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0679.s0 RH1E6S05_0679.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0679.s0 RH1E6S05_0679.rest = RH1E6S05_0679.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0679.s0 :: RH1E6S05_0679.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0679.s0.t = ((26167086915 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0679.s0]
  have e1 : RH1E6S05_0679.sL.t = ((26171824719 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0679.sL]
  rw [e0, e1] at h
  exact h

theorem part_084_3 : RS5.BandZeros ((26162349033 : ℝ) / 65536) ((26171824719 : ℝ) / 65536) 254 := by
  have g0 := band_0678
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0679
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((26162349033 : ℝ) / 65536) ((26171824719 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_084_3 <;> assumption
