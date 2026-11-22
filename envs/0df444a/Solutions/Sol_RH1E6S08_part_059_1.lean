-- Prove2me | solution 1 for RH1E6S08.part_059_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T06:49:04.461765+00:00
-- url     : https://prove2.me/submissions/412b0642-e4ed-4260-8e19-2474c914237d

import Definitions.Def_RH1E6S08_D059_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0474 : RS5.BandZeros ((34958318585 : ℝ) / 65536) ((34962927605 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0474.s0 RH1E6S08_0474.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0474.s0 RH1E6S08_0474.rest = RH1E6S08_0474.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0474.s0 :: RH1E6S08_0474.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0474.s0.t = ((34958318585 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0474.s0]
  have e1 : RH1E6S08_0474.sL.t = ((34962927605 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0474.sL]
  rw [e0, e1] at h
  exact h

theorem band_0475 : RS5.BandZeros ((34962927605 : ℝ) / 65536) ((34967549208 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0475.s0 RH1E6S08_0475.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0475.s0 RH1E6S08_0475.rest = RH1E6S08_0475.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0475.s0 :: RH1E6S08_0475.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0475.s0.t = ((34962927605 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0475.s0]
  have e1 : RH1E6S08_0475.sL.t = ((34967549208 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0475.sL]
  rw [e0, e1] at h
  exact h

theorem part_059_1 : RS5.BandZeros ((34958318585 : ℝ) / 65536) ((34967549208 : ℝ) / 65536) 254 := by
  have g0 := band_0474
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0475
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((34958318585 : ℝ) / 65536) ((34967549208 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_059_1 <;> assumption
