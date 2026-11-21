-- Prove2me | solution 1 for RH1E6S05.part_003_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:15:41.765816+00:00
-- url     : https://prove2.me/submissions/62711b15-cc93-4436-8614-e07b41ce6f8d

import Definitions.Def_RH1E6S05_D003_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0030 : RS5.BandZeros ((23081126360 : ℝ) / 65536) ((23085913825 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0030.s0 RH1E6S05_0030.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0030.s0 RH1E6S05_0030.rest = RH1E6S05_0030.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0030.s0 :: RH1E6S05_0030.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0030.s0.t = ((23081126360 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0030.s0]
  have e1 : RH1E6S05_0030.sL.t = ((23085913825 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0030.sL]
  rw [e0, e1] at h
  exact h

theorem band_0031 : RS5.BandZeros ((23085913825 : ℝ) / 65536) ((23090682371 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0031.s0 RH1E6S05_0031.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0031.s0 RH1E6S05_0031.rest = RH1E6S05_0031.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0031.s0 :: RH1E6S05_0031.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0031.s0.t = ((23085913825 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0031.s0]
  have e1 : RH1E6S05_0031.sL.t = ((23090682371 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0031.sL]
  rw [e0, e1] at h
  exact h

theorem part_003_3 : RS5.BandZeros ((23081126360 : ℝ) / 65536) ((23090682371 : ℝ) / 65536) 254 := by
  have g0 := band_0030
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0031
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((23081126360 : ℝ) / 65536) ((23090682371 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_003_3 <;> assumption
