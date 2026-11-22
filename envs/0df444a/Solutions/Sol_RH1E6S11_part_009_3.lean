-- Prove2me | solution 1 for RH1E6S11.part_009_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:29:12.025836+00:00
-- url     : https://prove2.me/submissions/9594e303-6150-47ae-85e1-4ea65fa4addf

import Definitions.Def_RH1E6S11_D009_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0078 : RS5.BandZeros ((42951530576 : ℝ) / 65536) ((42956047386 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0078.s0 RH1E6S11_0078.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0078.s0 RH1E6S11_0078.rest = RH1E6S11_0078.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0078.s0 :: RH1E6S11_0078.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0078.s0.t = ((42951530576 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0078.s0]
  have e1 : RH1E6S11_0078.sL.t = ((42956047386 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0078.sL]
  rw [e0, e1] at h
  exact h

theorem band_0079 : RS5.BandZeros ((42956047386 : ℝ) / 65536) ((42960590882 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0079.s0 RH1E6S11_0079.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0079.s0 RH1E6S11_0079.rest = RH1E6S11_0079.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0079.s0 :: RH1E6S11_0079.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0079.s0.t = ((42956047386 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0079.s0]
  have e1 : RH1E6S11_0079.sL.t = ((42960590882 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0079.sL]
  rw [e0, e1] at h
  exact h

theorem part_009_3 : RS5.BandZeros ((42951530576 : ℝ) / 65536) ((42960590882 : ℝ) / 65536) 254 := by
  have g0 := band_0078
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0079
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((42951530576 : ℝ) / 65536) ((42960590882 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_009_3 <;> assumption
