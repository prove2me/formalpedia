-- Prove2me | solution 1 for RH1E6S16.part_069_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:15:23.527208+00:00
-- url     : https://prove2.me/submissions/cf9c0fd5-1510-4abe-858e-dc4b75cd1d7c

import Definitions.Def_RH1E6S16_D069_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0554 : RS5.BandZeros ((61418497552 : ℝ) / 65536) ((61422863919 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0554.s0 RH1E6S16_0554.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0554.s0 RH1E6S16_0554.rest = RH1E6S16_0554.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0554.s0 :: RH1E6S16_0554.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0554.s0.t = ((61418497552 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0554.s0]
  have e1 : RH1E6S16_0554.sL.t = ((61422863919 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0554.sL]
  rw [e0, e1] at h
  exact h

theorem band_0555 : RS5.BandZeros ((61422863919 : ℝ) / 65536) ((61427262656 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0555.s0 RH1E6S16_0555.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0555.s0 RH1E6S16_0555.rest = RH1E6S16_0555.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0555.s0 :: RH1E6S16_0555.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0555.s0.t = ((61422863919 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0555.s0]
  have e1 : RH1E6S16_0555.sL.t = ((61427262656 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0555.sL]
  rw [e0, e1] at h
  exact h

theorem part_069_1 : RS5.BandZeros ((61418497552 : ℝ) / 65536) ((61427262656 : ℝ) / 65536) 254 := by
  have g0 := band_0554
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0555
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61418497552 : ℝ) / 65536) ((61427262656 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_069_1 <;> assumption
