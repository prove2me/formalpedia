-- Prove2me | solution 1 for RH1E6S07.part_086_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T03:51:08.64118+00:00
-- url     : https://prove2.me/submissions/ff30563c-f2f0-49f4-9c73-887eaed5762e

import Definitions.Def_RH1E6S07_D086_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0692 : RS5.BandZeros ((32713138464 : ℝ) / 65536) ((32717777727 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0692.s0 RH1E6S07_0692.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0692.s0 RH1E6S07_0692.rest = RH1E6S07_0692.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0692.s0 :: RH1E6S07_0692.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0692.s0.t = ((32713138464 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0692.s0]
  have e1 : RH1E6S07_0692.sL.t = ((32717777727 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0692.sL]
  rw [e0, e1] at h
  exact h

theorem band_0693 : RS5.BandZeros ((32717777727 : ℝ) / 65536) ((32722428344 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0693.s0 RH1E6S07_0693.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0693.s0 RH1E6S07_0693.rest = RH1E6S07_0693.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0693.s0 :: RH1E6S07_0693.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0693.s0.t = ((32717777727 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0693.s0]
  have e1 : RH1E6S07_0693.sL.t = ((32722428344 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0693.sL]
  rw [e0, e1] at h
  exact h

theorem part_086_2 : RS5.BandZeros ((32713138464 : ℝ) / 65536) ((32722428344 : ℝ) / 65536) 254 := by
  have g0 := band_0692
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0693
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((32713138464 : ℝ) / 65536) ((32722428344 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_086_2 <;> assumption
