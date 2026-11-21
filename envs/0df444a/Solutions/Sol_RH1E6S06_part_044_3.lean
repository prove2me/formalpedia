-- Prove2me | solution 1 for RH1E6S06.part_044_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T19:07:07.837414+00:00
-- url     : https://prove2.me/submissions/33778753-16ae-40fd-9c69-95f8e3cc1cb5

import Definitions.Def_RH1E6S06_D044_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0358 : RS5.BandZeros ((27902142714 : ℝ) / 65536) ((27906845490 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0358.s0 RH1E6S06_0358.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0358.s0 RH1E6S06_0358.rest = RH1E6S06_0358.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0358.s0 :: RH1E6S06_0358.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0358.s0.t = ((27902142714 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0358.s0]
  have e1 : RH1E6S06_0358.sL.t = ((27906845490 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0358.sL]
  rw [e0, e1] at h
  exact h

theorem band_0359 : RS5.BandZeros ((27906845490 : ℝ) / 65536) ((27911528221 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0359.s0 RH1E6S06_0359.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0359.s0 RH1E6S06_0359.rest = RH1E6S06_0359.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0359.s0 :: RH1E6S06_0359.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0359.s0.t = ((27906845490 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0359.s0]
  have e1 : RH1E6S06_0359.sL.t = ((27911528221 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0359.sL]
  rw [e0, e1] at h
  exact h

theorem part_044_3 : RS5.BandZeros ((27902142714 : ℝ) / 65536) ((27911528221 : ℝ) / 65536) 254 := by
  have g0 := band_0358
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0359
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27902142714 : ℝ) / 65536) ((27911528221 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_044_3 <;> assumption
