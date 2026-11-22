-- Prove2me | solution 1 for RH1E6S09.part_024_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:18:08.152096+00:00
-- url     : https://prove2.me/submissions/a7715349-d41c-4a85-a8d2-31d0f47b427d

import Definitions.Def_RH1E6S09_D024_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0198 : RS5.BandZeros ((36953671781 : ℝ) / 65536) ((36958263078 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0198.s0 RH1E6S09_0198.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0198.s0 RH1E6S09_0198.rest = RH1E6S09_0198.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0198.s0 :: RH1E6S09_0198.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0198.s0.t = ((36953671781 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0198.s0]
  have e1 : RH1E6S09_0198.sL.t = ((36958263078 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0198.sL]
  rw [e0, e1] at h
  exact h

theorem band_0199 : RS5.BandZeros ((36958263078 : ℝ) / 65536) ((36962850998 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0199.s0 RH1E6S09_0199.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0199.s0 RH1E6S09_0199.rest = RH1E6S09_0199.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0199.s0 :: RH1E6S09_0199.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0199.s0.t = ((36958263078 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0199.s0]
  have e1 : RH1E6S09_0199.sL.t = ((36962850998 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0199.sL]
  rw [e0, e1] at h
  exact h

theorem part_024_3 : RS5.BandZeros ((36953671781 : ℝ) / 65536) ((36962850998 : ℝ) / 65536) 254 := by
  have g0 := band_0198
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0199
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36953671781 : ℝ) / 65536) ((36962850998 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_024_3 <;> assumption
