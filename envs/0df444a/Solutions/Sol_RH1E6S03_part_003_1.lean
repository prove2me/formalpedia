-- Prove2me | solution 1 for RH1E6S03.part_003_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:24:00.566342+00:00
-- url     : https://prove2.me/submissions/237be17b-8719-4cba-a80e-bbc60902361d

import Definitions.Def_RH1E6S03_D003_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0026 : RS5.BandZeros ((16512324127 : ℝ) / 65536) ((16517257986 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0026.s0 RH1E6S03_0026.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0026.s0 RH1E6S03_0026.rest = RH1E6S03_0026.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0026.s0 :: RH1E6S03_0026.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0026.s0.t = ((16512324127 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0026.s0]
  have e1 : RH1E6S03_0026.sL.t = ((16517257986 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0026.sL]
  rw [e0, e1] at h
  exact h

theorem band_0027 : RS5.BandZeros ((16517257986 : ℝ) / 65536) ((16522201418 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0027.s0 RH1E6S03_0027.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0027.s0 RH1E6S03_0027.rest = RH1E6S03_0027.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0027.s0 :: RH1E6S03_0027.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0027.s0.t = ((16517257986 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0027.s0]
  have e1 : RH1E6S03_0027.sL.t = ((16522201418 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0027.sL]
  rw [e0, e1] at h
  exact h

theorem part_003_1 : RS5.BandZeros ((16512324127 : ℝ) / 65536) ((16522201418 : ℝ) / 65536) 254 := by
  have g0 := band_0026
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0027
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((16512324127 : ℝ) / 65536) ((16522201418 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_003_1 <;> assumption
