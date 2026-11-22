-- Prove2me | solution 1 for RH1E6S12.part_044_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T09:38:53.04602+00:00
-- url     : https://prove2.me/submissions/17ebdd4a-1233-422c-bbae-e79b41ffb145

import Definitions.Def_RH1E6S12_D044_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0358 : RS5.BandZeros ((47483858152 : ℝ) / 65536) ((47488329662 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0358.s0 RH1E6S12_0358.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0358.s0 RH1E6S12_0358.rest = RH1E6S12_0358.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0358.s0 :: RH1E6S12_0358.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0358.s0.t = ((47483858152 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0358.s0]
  have e1 : RH1E6S12_0358.sL.t = ((47488329662 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0358.sL]
  rw [e0, e1] at h
  exact h

theorem band_0359 : RS5.BandZeros ((47488329662 : ℝ) / 65536) ((47492834059 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0359.s0 RH1E6S12_0359.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0359.s0 RH1E6S12_0359.rest = RH1E6S12_0359.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0359.s0 :: RH1E6S12_0359.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0359.s0.t = ((47488329662 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0359.s0]
  have e1 : RH1E6S12_0359.sL.t = ((47492834059 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0359.sL]
  rw [e0, e1] at h
  exact h

theorem part_044_3 : RS5.BandZeros ((47483858152 : ℝ) / 65536) ((47492834059 : ℝ) / 65536) 254 := by
  have g0 := band_0358
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0359
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47483858152 : ℝ) / 65536) ((47492834059 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_044_3 <;> assumption
