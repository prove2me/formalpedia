-- Prove2me | solution 1 for RH1E6S09.part_036_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:51:04.554898+00:00
-- url     : https://prove2.me/submissions/ff24f5b1-6822-4ab6-8641-d96e533e4a7a

import Definitions.Def_RH1E6S09_D036_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0292 : RS5.BandZeros ((37384480067 : ℝ) / 65536) ((37389067373 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0292.s0 RH1E6S09_0292.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0292.s0 RH1E6S09_0292.rest = RH1E6S09_0292.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0292.s0 :: RH1E6S09_0292.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0292.s0.t = ((37384480067 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0292.s0]
  have e1 : RH1E6S09_0292.sL.t = ((37389067373 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0292.sL]
  rw [e0, e1] at h
  exact h

theorem band_0293 : RS5.BandZeros ((37389067373 : ℝ) / 65536) ((37393657927 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0293.s0 RH1E6S09_0293.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0293.s0 RH1E6S09_0293.rest = RH1E6S09_0293.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0293.s0 :: RH1E6S09_0293.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0293.s0.t = ((37389067373 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0293.s0]
  have e1 : RH1E6S09_0293.sL.t = ((37393657927 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0293.sL]
  rw [e0, e1] at h
  exact h

theorem part_036_2 : RS5.BandZeros ((37384480067 : ℝ) / 65536) ((37393657927 : ℝ) / 65536) 254 := by
  have g0 := band_0292
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0293
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37384480067 : ℝ) / 65536) ((37393657927 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_036_2 <;> assumption
