-- Prove2me | solution 1 for RH1E6S09.part_023_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:18:02.109194+00:00
-- url     : https://prove2.me/submissions/db924ac3-1edf-4fe4-b0b4-5b5e69ab7fe9

import Definitions.Def_RH1E6S09_D023_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0190 : RS5.BandZeros ((36917001597 : ℝ) / 65536) ((36921576119 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0190.s0 RH1E6S09_0190.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0190.s0 RH1E6S09_0190.rest = RH1E6S09_0190.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0190.s0 :: RH1E6S09_0190.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0190.s0.t = ((36917001597 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0190.s0]
  have e1 : RH1E6S09_0190.sL.t = ((36921576119 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0190.sL]
  rw [e0, e1] at h
  exact h

theorem band_0191 : RS5.BandZeros ((36921576119 : ℝ) / 65536) ((36926169443 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0191.s0 RH1E6S09_0191.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0191.s0 RH1E6S09_0191.rest = RH1E6S09_0191.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0191.s0 :: RH1E6S09_0191.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0191.s0.t = ((36921576119 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0191.s0]
  have e1 : RH1E6S09_0191.sL.t = ((36926169443 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0191.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_3 : RS5.BandZeros ((36917001597 : ℝ) / 65536) ((36926169443 : ℝ) / 65536) 254 := by
  have g0 := band_0190
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0191
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36917001597 : ℝ) / 65536) ((36926169443 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_023_3 <;> assumption
