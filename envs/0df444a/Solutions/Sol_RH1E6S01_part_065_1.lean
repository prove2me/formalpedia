-- Prove2me | solution 1 for RH1E6S01.part_065_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:37:10.279217+00:00
-- url     : https://prove2.me/submissions/a6137025-d22d-469b-925e-c85f92f3b076

import Definitions.Def_RH1E6S01_D065_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0522 : RS5.BandZeros ((12505201114 : ℝ) / 65536) ((12510267820 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0522.s0 RH1E6S01_0522.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0522.s0 RH1E6S01_0522.rest = RH1E6S01_0522.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0522.s0 :: RH1E6S01_0522.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0522.s0.t = ((12505201114 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0522.s0]
  have e1 : RH1E6S01_0522.sL.t = ((12510267820 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0522.sL]
  rw [e0, e1] at h
  exact h

theorem band_0523 : RS5.BandZeros ((12510267820 : ℝ) / 65536) ((12515334328 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0523.s0 RH1E6S01_0523.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0523.s0 RH1E6S01_0523.rest = RH1E6S01_0523.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0523.s0 :: RH1E6S01_0523.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0523.s0.t = ((12510267820 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0523.s0]
  have e1 : RH1E6S01_0523.sL.t = ((12515334328 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0523.sL]
  rw [e0, e1] at h
  exact h

theorem part_065_1 : RS5.BandZeros ((12505201114 : ℝ) / 65536) ((12515334328 : ℝ) / 65536) 254 := by
  have g0 := band_0522
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0523
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12505201114 : ℝ) / 65536) ((12515334328 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_065_1 <;> assumption
