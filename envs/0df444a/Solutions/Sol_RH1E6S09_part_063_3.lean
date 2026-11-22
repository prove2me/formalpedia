-- Prove2me | solution 1 for RH1E6S09.part_063_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T13:39:25.034007+00:00
-- url     : https://prove2.me/submissions/8396bcc0-6322-48e4-bd6c-dc98a10d3f40

import Definitions.Def_RH1E6S09_D063_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0510 : RS5.BandZeros ((38381941438 : ℝ) / 65536) ((38386504280 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0510.s0 RH1E6S09_0510.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0510.s0 RH1E6S09_0510.rest = RH1E6S09_0510.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0510.s0 :: RH1E6S09_0510.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0510.s0.t = ((38381941438 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0510.s0]
  have e1 : RH1E6S09_0510.sL.t = ((38386504280 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0510.sL]
  rw [e0, e1] at h
  exact h

theorem band_0511 : RS5.BandZeros ((38386504280 : ℝ) / 65536) ((38391092431 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0511.s0 RH1E6S09_0511.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0511.s0 RH1E6S09_0511.rest = RH1E6S09_0511.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0511.s0 :: RH1E6S09_0511.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0511.s0.t = ((38386504280 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0511.s0]
  have e1 : RH1E6S09_0511.sL.t = ((38391092431 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0511.sL]
  rw [e0, e1] at h
  exact h

theorem part_063_3 : RS5.BandZeros ((38381941438 : ℝ) / 65536) ((38391092431 : ℝ) / 65536) 254 := by
  have g0 := band_0510
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0511
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38381941438 : ℝ) / 65536) ((38391092431 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_063_3 <;> assumption
