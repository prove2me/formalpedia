-- Prove2me | solution 1 for RH1E6S14.part_028_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:08:03.636882+00:00
-- url     : https://prove2.me/submissions/90e8fc81-b39a-4708-9a78-8eca17d62d13

import Definitions.Def_RH1E6S14_D028_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0226 : RS5.BandZeros ((53433453710 : ℝ) / 65536) ((53437884946 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0226.s0 RH1E6S14_0226.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0226.s0 RH1E6S14_0226.rest = RH1E6S14_0226.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0226.s0 :: RH1E6S14_0226.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0226.s0.t = ((53433453710 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0226.s0]
  have e1 : RH1E6S14_0226.sL.t = ((53437884946 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0226.sL]
  rw [e0, e1] at h
  exact h

theorem band_0227 : RS5.BandZeros ((53437884946 : ℝ) / 65536) ((53442330332 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0227.s0 RH1E6S14_0227.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0227.s0 RH1E6S14_0227.rest = RH1E6S14_0227.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0227.s0 :: RH1E6S14_0227.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0227.s0.t = ((53437884946 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0227.s0]
  have e1 : RH1E6S14_0227.sL.t = ((53442330332 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0227.sL]
  rw [e0, e1] at h
  exact h

theorem part_028_1 : RS5.BandZeros ((53433453710 : ℝ) / 65536) ((53442330332 : ℝ) / 65536) 254 := by
  have g0 := band_0226
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0227
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53433453710 : ℝ) / 65536) ((53442330332 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_028_1 <;> assumption
