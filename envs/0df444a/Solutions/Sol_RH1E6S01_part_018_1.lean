-- Prove2me | solution 1 for RH1E6S01.part_018_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:58:34.510753+00:00
-- url     : https://prove2.me/submissions/e1945142-41b1-48a1-9769-7a762e27f641

import Definitions.Def_RH1E6S01_D018_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0146 : RS5.BandZeros ((10584995424 : ℝ) / 65536) ((10590155426 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0146.s0 RH1E6S01_0146.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0146.s0 RH1E6S01_0146.rest = RH1E6S01_0146.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0146.s0 :: RH1E6S01_0146.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0146.s0.t = ((10584995424 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0146.s0]
  have e1 : RH1E6S01_0146.sL.t = ((10590155426 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0146.sL]
  rw [e0, e1] at h
  exact h

theorem band_0147 : RS5.BandZeros ((10590155426 : ℝ) / 65536) ((10595325316 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0147.s0 RH1E6S01_0147.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0147.s0 RH1E6S01_0147.rest = RH1E6S01_0147.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0147.s0 :: RH1E6S01_0147.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0147.s0.t = ((10590155426 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0147.s0]
  have e1 : RH1E6S01_0147.sL.t = ((10595325316 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0147.sL]
  rw [e0, e1] at h
  exact h

theorem part_018_1 : RS5.BandZeros ((10584995424 : ℝ) / 65536) ((10595325316 : ℝ) / 65536) 254 := by
  have g0 := band_0146
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0147
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10584995424 : ℝ) / 65536) ((10595325316 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_018_1 <;> assumption
