-- Prove2me | solution 1 for RH1E6S15.part_032_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T09:44:54.191192+00:00
-- url     : https://prove2.me/submissions/9e6f478f-51d3-45fc-81ce-17d2744fe1f9

import Definitions.Def_RH1E6S15_D032_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0258 : RS5.BandZeros ((56846526727 : ℝ) / 65536) ((56850956276 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0258.s0 RH1E6S15_0258.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0258.s0 RH1E6S15_0258.rest = RH1E6S15_0258.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0258.s0 :: RH1E6S15_0258.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0258.s0.t = ((56846526727 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0258.s0]
  have e1 : RH1E6S15_0258.sL.t = ((56850956276 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0258.sL]
  rw [e0, e1] at h
  exact h

theorem band_0259 : RS5.BandZeros ((56850956276 : ℝ) / 65536) ((56855357399 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0259.s0 RH1E6S15_0259.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0259.s0 RH1E6S15_0259.rest = RH1E6S15_0259.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0259.s0 :: RH1E6S15_0259.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0259.s0.t = ((56850956276 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0259.s0]
  have e1 : RH1E6S15_0259.sL.t = ((56855357399 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0259.sL]
  rw [e0, e1] at h
  exact h

theorem part_032_1 : RS5.BandZeros ((56846526727 : ℝ) / 65536) ((56855357399 : ℝ) / 65536) 254 := by
  have g0 := band_0258
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0259
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56846526727 : ℝ) / 65536) ((56855357399 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_032_1 <;> assumption
