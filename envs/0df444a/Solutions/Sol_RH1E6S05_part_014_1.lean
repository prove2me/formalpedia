-- Prove2me | solution 1 for RH1E6S05.part_014_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:40:47.852174+00:00
-- url     : https://prove2.me/submissions/fb56121e-2dde-4d40-b14f-119a0a4548a1

import Definitions.Def_RH1E6S05_D014_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0114 : RS5.BandZeros ((23482564375 : ℝ) / 65536) ((23487349003 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0114.s0 RH1E6S05_0114.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0114.s0 RH1E6S05_0114.rest = RH1E6S05_0114.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0114.s0 :: RH1E6S05_0114.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0114.s0.t = ((23482564375 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0114.s0]
  have e1 : RH1E6S05_0114.sL.t = ((23487349003 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0114.sL]
  rw [e0, e1] at h
  exact h

theorem band_0115 : RS5.BandZeros ((23487349003 : ℝ) / 65536) ((23492095943 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0115.s0 RH1E6S05_0115.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0115.s0 RH1E6S05_0115.rest = RH1E6S05_0115.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0115.s0 :: RH1E6S05_0115.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0115.s0.t = ((23487349003 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0115.s0]
  have e1 : RH1E6S05_0115.sL.t = ((23492095943 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0115.sL]
  rw [e0, e1] at h
  exact h

theorem part_014_1 : RS5.BandZeros ((23482564375 : ℝ) / 65536) ((23492095943 : ℝ) / 65536) 254 := by
  have g0 := band_0114
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0115
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((23482564375 : ℝ) / 65536) ((23492095943 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_014_1 <;> assumption
