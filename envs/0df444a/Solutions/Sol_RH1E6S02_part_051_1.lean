-- Prove2me | solution 1 for RH1E6S02.part_051_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:56:28.822359+00:00
-- url     : https://prove2.me/submissions/3993f915-d053-4f7b-a281-8992a3c427a7

import Definitions.Def_RH1E6S02_D051_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0410 : RS5.BandZeros ((15160409204 : ℝ) / 65536) ((15165405583 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0410.s0 RH1E6S02_0410.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0410.s0 RH1E6S02_0410.rest = RH1E6S02_0410.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0410.s0 :: RH1E6S02_0410.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0410.s0.t = ((15160409204 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0410.s0]
  have e1 : RH1E6S02_0410.sL.t = ((15165405583 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0410.sL]
  rw [e0, e1] at h
  exact h

theorem band_0411 : RS5.BandZeros ((15165405583 : ℝ) / 65536) ((15170366714 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0411.s0 RH1E6S02_0411.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0411.s0 RH1E6S02_0411.rest = RH1E6S02_0411.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0411.s0 :: RH1E6S02_0411.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0411.s0.t = ((15165405583 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0411.s0]
  have e1 : RH1E6S02_0411.sL.t = ((15170366714 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0411.sL]
  rw [e0, e1] at h
  exact h

theorem part_051_1 : RS5.BandZeros ((15160409204 : ℝ) / 65536) ((15170366714 : ℝ) / 65536) 254 := by
  have g0 := band_0410
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0411
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((15160409204 : ℝ) / 65536) ((15170366714 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_051_1 <;> assumption
