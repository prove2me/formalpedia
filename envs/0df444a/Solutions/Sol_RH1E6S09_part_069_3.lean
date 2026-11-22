-- Prove2me | solution 1 for RH1E6S09.part_069_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T14:21:03.828153+00:00
-- url     : https://prove2.me/submissions/01e91d90-e7de-4ff6-ab2c-c5225a67f0f3

import Definitions.Def_RH1E6S09_D069_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0558 : RS5.BandZeros ((38601257798 : ℝ) / 65536) ((38605827361 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0558.s0 RH1E6S09_0558.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0558.s0 RH1E6S09_0558.rest = RH1E6S09_0558.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0558.s0 :: RH1E6S09_0558.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0558.s0.t = ((38601257798 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0558.s0]
  have e1 : RH1E6S09_0558.sL.t = ((38605827361 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0558.sL]
  rw [e0, e1] at h
  exact h

theorem band_0559 : RS5.BandZeros ((38605827361 : ℝ) / 65536) ((38610398937 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0559.s0 RH1E6S09_0559.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0559.s0 RH1E6S09_0559.rest = RH1E6S09_0559.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0559.s0 :: RH1E6S09_0559.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0559.s0.t = ((38605827361 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0559.s0]
  have e1 : RH1E6S09_0559.sL.t = ((38610398937 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0559.sL]
  rw [e0, e1] at h
  exact h

theorem part_069_3 : RS5.BandZeros ((38601257798 : ℝ) / 65536) ((38610398937 : ℝ) / 65536) 254 := by
  have g0 := band_0558
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0559
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38601257798 : ℝ) / 65536) ((38610398937 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_069_3 <;> assumption
