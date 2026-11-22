-- Prove2me | solution 1 for RH1E6S09.part_058_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:50:35.738791+00:00
-- url     : https://prove2.me/submissions/75b13ce2-5402-4bd3-bd84-5e32f39f3322

import Definitions.Def_RH1E6S09_D058_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0464 : RS5.BandZeros ((38171655643 : ℝ) / 65536) ((38176234483 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0464.s0 RH1E6S09_0464.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0464.s0 RH1E6S09_0464.rest = RH1E6S09_0464.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0464.s0 :: RH1E6S09_0464.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0464.s0.t = ((38171655643 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0464.s0]
  have e1 : RH1E6S09_0464.sL.t = ((38176234483 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0464.sL]
  rw [e0, e1] at h
  exact h

theorem band_0465 : RS5.BandZeros ((38176234483 : ℝ) / 65536) ((38180811931 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0465.s0 RH1E6S09_0465.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0465.s0 RH1E6S09_0465.rest = RH1E6S09_0465.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0465.s0 :: RH1E6S09_0465.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0465.s0.t = ((38176234483 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0465.s0]
  have e1 : RH1E6S09_0465.sL.t = ((38180811931 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0465.sL]
  rw [e0, e1] at h
  exact h

theorem part_058_0 : RS5.BandZeros ((38171655643 : ℝ) / 65536) ((38180811931 : ℝ) / 65536) 254 := by
  have g0 := band_0464
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0465
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38171655643 : ℝ) / 65536) ((38180811931 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_058_0 <;> assumption
