-- Prove2me | solution 1 for RH1E6S09.part_054_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:42:23.147918+00:00
-- url     : https://prove2.me/submissions/1e2677f3-b5e3-4c90-b773-a338d95639d4

import Definitions.Def_RH1E6S09_D054_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0438 : RS5.BandZeros ((38052753828 : ℝ) / 65536) ((38057332359 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0438.s0 RH1E6S09_0438.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0438.s0 RH1E6S09_0438.rest = RH1E6S09_0438.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0438.s0 :: RH1E6S09_0438.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0438.s0.t = ((38052753828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0438.s0]
  have e1 : RH1E6S09_0438.sL.t = ((38057332359 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0438.sL]
  rw [e0, e1] at h
  exact h

theorem band_0439 : RS5.BandZeros ((38057332359 : ℝ) / 65536) ((38061903720 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0439.s0 RH1E6S09_0439.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0439.s0 RH1E6S09_0439.rest = RH1E6S09_0439.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0439.s0 :: RH1E6S09_0439.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0439.s0.t = ((38057332359 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0439.s0]
  have e1 : RH1E6S09_0439.sL.t = ((38061903720 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0439.sL]
  rw [e0, e1] at h
  exact h

theorem part_054_3 : RS5.BandZeros ((38052753828 : ℝ) / 65536) ((38061903720 : ℝ) / 65536) 254 := by
  have g0 := band_0438
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0439
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38052753828 : ℝ) / 65536) ((38061903720 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_054_3 <;> assumption
