-- Prove2me | solution 1 for RH1E6S13.part_053_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T23:46:26.491531+00:00
-- url     : https://prove2.me/submissions/2294855a-201f-4cd7-b338-7fe408265166

import Definitions.Def_RH1E6S13_D053_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0424 : RS5.BandZeros ((51045712119 : ℝ) / 65536) ((51050162439 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0424.s0 RH1E6S13_0424.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0424.s0 RH1E6S13_0424.rest = RH1E6S13_0424.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0424.s0 :: RH1E6S13_0424.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0424.s0.t = ((51045712119 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0424.s0]
  have e1 : RH1E6S13_0424.sL.t = ((51050162439 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0424.sL]
  rw [e0, e1] at h
  exact h

theorem band_0425 : RS5.BandZeros ((51050162439 : ℝ) / 65536) ((51054630282 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0425.s0 RH1E6S13_0425.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0425.s0 RH1E6S13_0425.rest = RH1E6S13_0425.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0425.s0 :: RH1E6S13_0425.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0425.s0.t = ((51050162439 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0425.s0]
  have e1 : RH1E6S13_0425.sL.t = ((51054630282 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0425.sL]
  rw [e0, e1] at h
  exact h

theorem part_053_0 : RS5.BandZeros ((51045712119 : ℝ) / 65536) ((51054630282 : ℝ) / 65536) 254 := by
  have g0 := band_0424
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0425
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51045712119 : ℝ) / 65536) ((51054630282 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_053_0 <;> assumption
