-- Prove2me | solution 1 for RH1E6S07.part_040_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T00:50:03.323855+00:00
-- url     : https://prove2.me/submissions/de0cc28f-5cbb-4dbd-aada-df6767c87c8a

import Definitions.Def_RH1E6S07_D040_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0322 : RS5.BandZeros ((30994119984 : ℝ) / 65536) ((30998768029 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0322.s0 RH1E6S07_0322.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0322.s0 RH1E6S07_0322.rest = RH1E6S07_0322.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0322.s0 :: RH1E6S07_0322.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0322.s0.t = ((30994119984 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0322.s0]
  have e1 : RH1E6S07_0322.sL.t = ((30998768029 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0322.sL]
  rw [e0, e1] at h
  exact h

theorem band_0323 : RS5.BandZeros ((30998768029 : ℝ) / 65536) ((31003438491 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0323.s0 RH1E6S07_0323.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0323.s0 RH1E6S07_0323.rest = RH1E6S07_0323.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0323.s0 :: RH1E6S07_0323.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0323.s0.t = ((30998768029 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0323.s0]
  have e1 : RH1E6S07_0323.sL.t = ((31003438491 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0323.sL]
  rw [e0, e1] at h
  exact h

theorem part_040_1 : RS5.BandZeros ((30994119984 : ℝ) / 65536) ((31003438491 : ℝ) / 65536) 254 := by
  have g0 := band_0322
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0323
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30994119984 : ℝ) / 65536) ((31003438491 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_040_1 <;> assumption
