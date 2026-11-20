-- Prove2me | solution 1 for RH1E6S01.part_023_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:10:19.663759+00:00
-- url     : https://prove2.me/submissions/08620abd-71b6-4209-8256-f5d4f8959a41

import Definitions.Def_RH1E6S01_D023_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0190 : RS5.BandZeros ((10811358209 : ℝ) / 65536) ((10816507484 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0190.s0 RH1E6S01_0190.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0190.s0 RH1E6S01_0190.rest = RH1E6S01_0190.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0190.s0 :: RH1E6S01_0190.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0190.s0.t = ((10811358209 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0190.s0]
  have e1 : RH1E6S01_0190.sL.t = ((10816507484 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0190.sL]
  rw [e0, e1] at h
  exact h

theorem band_0191 : RS5.BandZeros ((10816507484 : ℝ) / 65536) ((10821656518 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0191.s0 RH1E6S01_0191.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0191.s0 RH1E6S01_0191.rest = RH1E6S01_0191.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0191.s0 :: RH1E6S01_0191.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0191.s0.t = ((10816507484 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0191.s0]
  have e1 : RH1E6S01_0191.sL.t = ((10821656518 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0191.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_3 : RS5.BandZeros ((10811358209 : ℝ) / 65536) ((10821656518 : ℝ) / 65536) 254 := by
  have g0 := band_0190
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0191
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10811358209 : ℝ) / 65536) ((10821656518 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_023_3 <;> assumption
