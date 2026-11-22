-- Prove2me | solution 1 for RH1E6S09.part_054_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:42:21.113454+00:00
-- url     : https://prove2.me/submissions/16fb82ae-ed9c-4f62-95ad-49fa337df9de

import Definitions.Def_RH1E6S09_D054_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0436 : RS5.BandZeros ((38043623638 : ℝ) / 65536) ((38048193524 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0436.s0 RH1E6S09_0436.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0436.s0 RH1E6S09_0436.rest = RH1E6S09_0436.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0436.s0 :: RH1E6S09_0436.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0436.s0.t = ((38043623638 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0436.s0]
  have e1 : RH1E6S09_0436.sL.t = ((38048193524 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0436.sL]
  rw [e0, e1] at h
  exact h

theorem band_0437 : RS5.BandZeros ((38048193524 : ℝ) / 65536) ((38052753828 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0437.s0 RH1E6S09_0437.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0437.s0 RH1E6S09_0437.rest = RH1E6S09_0437.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0437.s0 :: RH1E6S09_0437.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0437.s0.t = ((38048193524 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0437.s0]
  have e1 : RH1E6S09_0437.sL.t = ((38052753828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0437.sL]
  rw [e0, e1] at h
  exact h

theorem part_054_2 : RS5.BandZeros ((38043623638 : ℝ) / 65536) ((38052753828 : ℝ) / 65536) 254 := by
  have g0 := band_0436
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0437
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38043623638 : ℝ) / 65536) ((38052753828 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_054_2 <;> assumption
