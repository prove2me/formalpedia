-- Prove2me | solution 1 for RH1E6S08.part_044_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T06:08:12.258507+00:00
-- url     : https://prove2.me/submissions/b0e24746-00c8-482d-bbe8-c0298984a81d

import Definitions.Def_RH1E6S08_D044_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0358 : RS5.BandZeros ((34423446614 : ℝ) / 65536) ((34428065289 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0358.s0 RH1E6S08_0358.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0358.s0 RH1E6S08_0358.rest = RH1E6S08_0358.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0358.s0 :: RH1E6S08_0358.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0358.s0.t = ((34423446614 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0358.s0]
  have e1 : RH1E6S08_0358.sL.t = ((34428065289 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0358.sL]
  rw [e0, e1] at h
  exact h

theorem band_0359 : RS5.BandZeros ((34428065289 : ℝ) / 65536) ((34432693451 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0359.s0 RH1E6S08_0359.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0359.s0 RH1E6S08_0359.rest = RH1E6S08_0359.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0359.s0 :: RH1E6S08_0359.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0359.s0.t = ((34428065289 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0359.s0]
  have e1 : RH1E6S08_0359.sL.t = ((34432693451 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0359.sL]
  rw [e0, e1] at h
  exact h

theorem part_044_3 : RS5.BandZeros ((34423446614 : ℝ) / 65536) ((34432693451 : ℝ) / 65536) 254 := by
  have g0 := band_0358
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0359
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((34423446614 : ℝ) / 65536) ((34432693451 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_044_3 <;> assumption
