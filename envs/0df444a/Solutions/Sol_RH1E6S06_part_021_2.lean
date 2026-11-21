-- Prove2me | solution 1 for RH1E6S06.part_021_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:06:38.332475+00:00
-- url     : https://prove2.me/submissions/4789bb13-67e4-49d5-bbaa-3a647ef046db

import Definitions.Def_RH1E6S06_D021_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0172 : RS5.BandZeros ((27026464573 : ℝ) / 65536) ((27031170014 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0172.s0 RH1E6S06_0172.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0172.s0 RH1E6S06_0172.rest = RH1E6S06_0172.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0172.s0 :: RH1E6S06_0172.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0172.s0.t = ((27026464573 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0172.s0]
  have e1 : RH1E6S06_0172.sL.t = ((27031170014 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0172.sL]
  rw [e0, e1] at h
  exact h

theorem band_0173 : RS5.BandZeros ((27031170014 : ℝ) / 65536) ((27035869393 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0173.s0 RH1E6S06_0173.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0173.s0 RH1E6S06_0173.rest = RH1E6S06_0173.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0173.s0 :: RH1E6S06_0173.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0173.s0.t = ((27031170014 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0173.s0]
  have e1 : RH1E6S06_0173.sL.t = ((27035869393 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0173.sL]
  rw [e0, e1] at h
  exact h

theorem part_021_2 : RS5.BandZeros ((27026464573 : ℝ) / 65536) ((27035869393 : ℝ) / 65536) 254 := by
  have g0 := band_0172
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0173
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27026464573 : ℝ) / 65536) ((27035869393 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_021_2 <;> assumption
