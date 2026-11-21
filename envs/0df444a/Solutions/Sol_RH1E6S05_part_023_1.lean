-- Prove2me | solution 1 for RH1E6S05.part_023_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T13:01:09.823556+00:00
-- url     : https://prove2.me/submissions/e5369dbf-7164-46a2-a563-6c049e171e7b

import Definitions.Def_RH1E6S05_D023_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0186 : RS5.BandZeros ((23826155573 : ℝ) / 65536) ((23830915089 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0186.s0 RH1E6S05_0186.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0186.s0 RH1E6S05_0186.rest = RH1E6S05_0186.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0186.s0 :: RH1E6S05_0186.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0186.s0.t = ((23826155573 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0186.s0]
  have e1 : RH1E6S05_0186.sL.t = ((23830915089 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0186.sL]
  rw [e0, e1] at h
  exact h

theorem band_0187 : RS5.BandZeros ((23830915089 : ℝ) / 65536) ((23835683906 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0187.s0 RH1E6S05_0187.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0187.s0 RH1E6S05_0187.rest = RH1E6S05_0187.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0187.s0 :: RH1E6S05_0187.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0187.s0.t = ((23830915089 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0187.s0]
  have e1 : RH1E6S05_0187.sL.t = ((23835683906 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0187.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_1 : RS5.BandZeros ((23826155573 : ℝ) / 65536) ((23835683906 : ℝ) / 65536) 254 := by
  have g0 := band_0186
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0187
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((23826155573 : ℝ) / 65536) ((23835683906 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_023_1 <;> assumption
