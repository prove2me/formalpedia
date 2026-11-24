-- Prove2me | solution 1 for RH1E6S17.part_063_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T23:10:44.094252+00:00
-- url     : https://prove2.me/submissions/b009c832-ffa6-4516-99d0-76e0b53b8d78

import Definitions.Def_RH1E6S17_D063_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0510 : RS5.BandZeros ((64492167862 : ℝ) / 65536) ((64496557011 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0510.s0 RH1E6S17_0510.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0510.s0 RH1E6S17_0510.rest = RH1E6S17_0510.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0510.s0 :: RH1E6S17_0510.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0510.s0.t = ((64492167862 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0510.s0]
  have e1 : RH1E6S17_0510.sL.t = ((64496557011 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0510.sL]
  rw [e0, e1] at h
  exact h

theorem band_0511 : RS5.BandZeros ((64496557011 : ℝ) / 65536) ((64500911710 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0511.s0 RH1E6S17_0511.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0511.s0 RH1E6S17_0511.rest = RH1E6S17_0511.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0511.s0 :: RH1E6S17_0511.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0511.s0.t = ((64496557011 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0511.s0]
  have e1 : RH1E6S17_0511.sL.t = ((64500911710 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0511.sL]
  rw [e0, e1] at h
  exact h

theorem part_063_3 : RS5.BandZeros ((64492167862 : ℝ) / 65536) ((64500911710 : ℝ) / 65536) 254 := by
  have g0 := band_0510
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0511
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64492167862 : ℝ) / 65536) ((64500911710 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_063_3 <;> assumption
