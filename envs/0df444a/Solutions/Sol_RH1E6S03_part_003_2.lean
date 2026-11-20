-- Prove2me | solution 1 for RH1E6S03.part_003_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:24:02.599608+00:00
-- url     : https://prove2.me/submissions/1e54a6c5-e110-408d-aa6a-f677504b8bd7

import Definitions.Def_RH1E6S03_D003_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0028 : RS5.BandZeros ((16522201418 : ℝ) / 65536) ((16527125287 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0028.s0 RH1E6S03_0028.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0028.s0 RH1E6S03_0028.rest = RH1E6S03_0028.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0028.s0 :: RH1E6S03_0028.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0028.s0.t = ((16522201418 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0028.s0]
  have e1 : RH1E6S03_0028.sL.t = ((16527125287 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0028.sL]
  rw [e0, e1] at h
  exact h

theorem band_0029 : RS5.BandZeros ((16527125287 : ℝ) / 65536) ((16532058729 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0029.s0 RH1E6S03_0029.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0029.s0 RH1E6S03_0029.rest = RH1E6S03_0029.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0029.s0 :: RH1E6S03_0029.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0029.s0.t = ((16527125287 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0029.s0]
  have e1 : RH1E6S03_0029.sL.t = ((16532058729 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0029.sL]
  rw [e0, e1] at h
  exact h

theorem part_003_2 : RS5.BandZeros ((16522201418 : ℝ) / 65536) ((16532058729 : ℝ) / 65536) 254 := by
  have g0 := band_0028
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0029
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((16522201418 : ℝ) / 65536) ((16532058729 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_003_2 <;> assumption
