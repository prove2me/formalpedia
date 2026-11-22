-- Prove2me | solution 1 for RH1E6S09.part_011_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T08:42:04.628755+00:00
-- url     : https://prove2.me/submissions/c8501f8e-6ced-4e39-8fb8-b3e5802da12f

import Definitions.Def_RH1E6S09_D011_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0088 : RS5.BandZeros ((36448985351 : ℝ) / 65536) ((36453552153 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0088.s0 RH1E6S09_0088.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0088.s0 RH1E6S09_0088.rest = RH1E6S09_0088.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0088.s0 :: RH1E6S09_0088.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0088.s0.t = ((36448985351 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0088.s0]
  have e1 : RH1E6S09_0088.sL.t = ((36453552153 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0088.sL]
  rw [e0, e1] at h
  exact h

theorem band_0089 : RS5.BandZeros ((36453552153 : ℝ) / 65536) ((36458170151 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0089.s0 RH1E6S09_0089.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0089.s0 RH1E6S09_0089.rest = RH1E6S09_0089.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0089.s0 :: RH1E6S09_0089.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0089.s0.t = ((36453552153 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0089.s0]
  have e1 : RH1E6S09_0089.sL.t = ((36458170151 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0089.sL]
  rw [e0, e1] at h
  exact h

theorem part_011_0 : RS5.BandZeros ((36448985351 : ℝ) / 65536) ((36458170151 : ℝ) / 65536) 254 := by
  have g0 := band_0088
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0089
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36448985351 : ℝ) / 65536) ((36458170151 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_011_0 <;> assumption
