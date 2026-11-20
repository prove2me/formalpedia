-- Prove2me | solution 1 for RH1E6S01.part_045_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:55:12.380149+00:00
-- url     : https://prove2.me/submissions/e7c1b2dc-e9bb-491c-a059-5a7cfd5a8b57

import Definitions.Def_RH1E6S01_D045_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0362 : RS5.BandZeros ((11691902365 : ℝ) / 65536) ((11696992252 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0362.s0 RH1E6S01_0362.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0362.s0 RH1E6S01_0362.rest = RH1E6S01_0362.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0362.s0 :: RH1E6S01_0362.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0362.s0.t = ((11691902365 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0362.s0]
  have e1 : RH1E6S01_0362.sL.t = ((11696992252 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0362.sL]
  rw [e0, e1] at h
  exact h

theorem band_0363 : RS5.BandZeros ((11696992252 : ℝ) / 65536) ((11702112040 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0363.s0 RH1E6S01_0363.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0363.s0 RH1E6S01_0363.rest = RH1E6S01_0363.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0363.s0 :: RH1E6S01_0363.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0363.s0.t = ((11696992252 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0363.s0]
  have e1 : RH1E6S01_0363.sL.t = ((11702112040 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0363.sL]
  rw [e0, e1] at h
  exact h

theorem part_045_1 : RS5.BandZeros ((11691902365 : ℝ) / 65536) ((11702112040 : ℝ) / 65536) 254 := by
  have g0 := band_0362
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0363
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11691902365 : ℝ) / 65536) ((11702112040 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_045_1 <;> assumption
