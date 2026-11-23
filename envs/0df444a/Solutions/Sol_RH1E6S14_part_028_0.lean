-- Prove2me | solution 1 for RH1E6S14.part_028_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:08:01.612829+00:00
-- url     : https://prove2.me/submissions/4df769cf-16c0-4211-838d-02ee139c61c0

import Definitions.Def_RH1E6S14_D028_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0224 : RS5.BandZeros ((53424576598 : ℝ) / 65536) ((53429002687 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0224.s0 RH1E6S14_0224.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0224.s0 RH1E6S14_0224.rest = RH1E6S14_0224.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0224.s0 :: RH1E6S14_0224.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0224.s0.t = ((53424576598 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0224.s0]
  have e1 : RH1E6S14_0224.sL.t = ((53429002687 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0224.sL]
  rw [e0, e1] at h
  exact h

theorem band_0225 : RS5.BandZeros ((53429002687 : ℝ) / 65536) ((53433453710 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0225.s0 RH1E6S14_0225.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0225.s0 RH1E6S14_0225.rest = RH1E6S14_0225.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0225.s0 :: RH1E6S14_0225.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0225.s0.t = ((53429002687 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0225.s0]
  have e1 : RH1E6S14_0225.sL.t = ((53433453710 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0225.sL]
  rw [e0, e1] at h
  exact h

theorem part_028_0 : RS5.BandZeros ((53424576598 : ℝ) / 65536) ((53433453710 : ℝ) / 65536) 254 := by
  have g0 := band_0224
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0225
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53424576598 : ℝ) / 65536) ((53433453710 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_028_0 <;> assumption
