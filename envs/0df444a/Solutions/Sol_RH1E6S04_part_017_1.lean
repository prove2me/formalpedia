-- Prove2me | solution 1 for RH1E6S04.part_017_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:03:08.272395+00:00
-- url     : https://prove2.me/submissions/d80d80bf-411a-4467-ae14-10717e5f6846

import Definitions.Def_RH1E6S04_D017_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0138 : RS5.BandZeros ((20329625824 : ℝ) / 65536) ((20334464750 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0138.s0 RH1E6S04_0138.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0138.s0 RH1E6S04_0138.rest = RH1E6S04_0138.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0138.s0 :: RH1E6S04_0138.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0138.s0.t = ((20329625824 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0138.s0]
  have e1 : RH1E6S04_0138.sL.t = ((20334464750 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0138.sL]
  rw [e0, e1] at h
  exact h

theorem band_0139 : RS5.BandZeros ((20334464750 : ℝ) / 65536) ((20339294045 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0139.s0 RH1E6S04_0139.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0139.s0 RH1E6S04_0139.rest = RH1E6S04_0139.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0139.s0 :: RH1E6S04_0139.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0139.s0.t = ((20334464750 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0139.s0]
  have e1 : RH1E6S04_0139.sL.t = ((20339294045 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0139.sL]
  rw [e0, e1] at h
  exact h

theorem part_017_1 : RS5.BandZeros ((20329625824 : ℝ) / 65536) ((20339294045 : ℝ) / 65536) 254 := by
  have g0 := band_0138
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0139
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20329625824 : ℝ) / 65536) ((20339294045 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_017_1 <;> assumption
