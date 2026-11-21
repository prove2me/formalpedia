-- Prove2me | solution 1 for RH1E6S04.part_023_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:15:38.013629+00:00
-- url     : https://prove2.me/submissions/d159f2e2-ded8-4b56-8251-b815044e0f7a

import Definitions.Def_RH1E6S04_D023_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0186 : RS5.BandZeros ((20561765161 : ℝ) / 65536) ((20566599010 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0186.s0 RH1E6S04_0186.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0186.s0 RH1E6S04_0186.rest = RH1E6S04_0186.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0186.s0 :: RH1E6S04_0186.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0186.s0.t = ((20561765161 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0186.s0]
  have e1 : RH1E6S04_0186.sL.t = ((20566599010 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0186.sL]
  rw [e0, e1] at h
  exact h

theorem band_0187 : RS5.BandZeros ((20566599010 : ℝ) / 65536) ((20571442269 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0187.s0 RH1E6S04_0187.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0187.s0 RH1E6S04_0187.rest = RH1E6S04_0187.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0187.s0 :: RH1E6S04_0187.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0187.s0.t = ((20566599010 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0187.s0]
  have e1 : RH1E6S04_0187.sL.t = ((20571442269 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0187.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_1 : RS5.BandZeros ((20561765161 : ℝ) / 65536) ((20571442269 : ℝ) / 65536) 254 := by
  have g0 := band_0186
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0187
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20561765161 : ℝ) / 65536) ((20571442269 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_023_1 <;> assumption
