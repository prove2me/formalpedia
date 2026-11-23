-- Prove2me | solution 1 for RH1E6S16.part_076_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:40:31.349645+00:00
-- url     : https://prove2.me/submissions/d9db474a-e51b-42f4-8ebf-0756d3d09df2

import Definitions.Def_RH1E6S16_D076_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0614 : RS5.BandZeros ((61681824273 : ℝ) / 65536) ((61686230454 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0614.s0 RH1E6S16_0614.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0614.s0 RH1E6S16_0614.rest = RH1E6S16_0614.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0614.s0 :: RH1E6S16_0614.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0614.s0.t = ((61681824273 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0614.s0]
  have e1 : RH1E6S16_0614.sL.t = ((61686230454 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0614.sL]
  rw [e0, e1] at h
  exact h

theorem band_0615 : RS5.BandZeros ((61686230454 : ℝ) / 65536) ((61690618227 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0615.s0 RH1E6S16_0615.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0615.s0 RH1E6S16_0615.rest = RH1E6S16_0615.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0615.s0 :: RH1E6S16_0615.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0615.s0.t = ((61686230454 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0615.s0]
  have e1 : RH1E6S16_0615.sL.t = ((61690618227 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0615.sL]
  rw [e0, e1] at h
  exact h

theorem part_076_3 : RS5.BandZeros ((61681824273 : ℝ) / 65536) ((61690618227 : ℝ) / 65536) 254 := by
  have g0 := band_0614
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0615
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61681824273 : ℝ) / 65536) ((61690618227 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_076_3 <;> assumption
