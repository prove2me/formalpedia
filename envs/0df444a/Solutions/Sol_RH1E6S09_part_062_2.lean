-- Prove2me | solution 1 for RH1E6S09.part_062_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T13:33:42.69816+00:00
-- url     : https://prove2.me/submissions/5d55361b-4b31-4846-9c24-c0328b9cf922

import Definitions.Def_RH1E6S09_D062_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0500 : RS5.BandZeros ((38336233561 : ℝ) / 65536) ((38340800081 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0500.s0 RH1E6S09_0500.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0500.s0 RH1E6S09_0500.rest = RH1E6S09_0500.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0500.s0 :: RH1E6S09_0500.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0500.s0.t = ((38336233561 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0500.s0]
  have e1 : RH1E6S09_0500.sL.t = ((38340800081 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0500.sL]
  rw [e0, e1] at h
  exact h

theorem band_0501 : RS5.BandZeros ((38340800081 : ℝ) / 65536) ((38345394837 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0501.s0 RH1E6S09_0501.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0501.s0 RH1E6S09_0501.rest = RH1E6S09_0501.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0501.s0 :: RH1E6S09_0501.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0501.s0.t = ((38340800081 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0501.s0]
  have e1 : RH1E6S09_0501.sL.t = ((38345394837 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0501.sL]
  rw [e0, e1] at h
  exact h

theorem part_062_2 : RS5.BandZeros ((38336233561 : ℝ) / 65536) ((38345394837 : ℝ) / 65536) 254 := by
  have g0 := band_0500
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0501
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38336233561 : ℝ) / 65536) ((38345394837 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_062_2 <;> assumption
