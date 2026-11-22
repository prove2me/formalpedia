-- Prove2me | solution 1 for RH1E6S08.part_060_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T06:51:51.030653+00:00
-- url     : https://prove2.me/submissions/23cd5063-1160-484c-9219-5d115e2400e4

import Definitions.Def_RH1E6S08_D060_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0484 : RS5.BandZeros ((35004397334 : ℝ) / 65536) ((35009007688 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0484.s0 RH1E6S08_0484.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0484.s0 RH1E6S08_0484.rest = RH1E6S08_0484.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0484.s0 :: RH1E6S08_0484.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0484.s0.t = ((35004397334 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0484.s0]
  have e1 : RH1E6S08_0484.sL.t = ((35009007688 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0484.sL]
  rw [e0, e1] at h
  exact h

theorem band_0485 : RS5.BandZeros ((35009007688 : ℝ) / 65536) ((35013621392 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0485.s0 RH1E6S08_0485.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0485.s0 RH1E6S08_0485.rest = RH1E6S08_0485.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0485.s0 :: RH1E6S08_0485.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0485.s0.t = ((35009007688 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0485.s0]
  have e1 : RH1E6S08_0485.sL.t = ((35013621392 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0485.sL]
  rw [e0, e1] at h
  exact h

theorem part_060_2 : RS5.BandZeros ((35004397334 : ℝ) / 65536) ((35013621392 : ℝ) / 65536) 254 := by
  have g0 := band_0484
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0485
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35004397334 : ℝ) / 65536) ((35013621392 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_060_2 <;> assumption
