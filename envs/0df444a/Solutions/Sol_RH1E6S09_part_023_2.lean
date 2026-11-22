-- Prove2me | solution 1 for RH1E6S09.part_023_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:15:01.542602+00:00
-- url     : https://prove2.me/submissions/f4ffaaf5-e461-4d82-ac16-ab0e17b59433

import Definitions.Def_RH1E6S09_D023_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0188 : RS5.BandZeros ((36907816060 : ℝ) / 65536) ((36912408881 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0188.s0 RH1E6S09_0188.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0188.s0 RH1E6S09_0188.rest = RH1E6S09_0188.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0188.s0 :: RH1E6S09_0188.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0188.s0.t = ((36907816060 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0188.s0]
  have e1 : RH1E6S09_0188.sL.t = ((36912408881 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0188.sL]
  rw [e0, e1] at h
  exact h

theorem band_0189 : RS5.BandZeros ((36912408881 : ℝ) / 65536) ((36917001597 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0189.s0 RH1E6S09_0189.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0189.s0 RH1E6S09_0189.rest = RH1E6S09_0189.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0189.s0 :: RH1E6S09_0189.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0189.s0.t = ((36912408881 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0189.s0]
  have e1 : RH1E6S09_0189.sL.t = ((36917001597 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0189.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_2 : RS5.BandZeros ((36907816060 : ℝ) / 65536) ((36917001597 : ℝ) / 65536) 254 := by
  have g0 := band_0188
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0189
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36907816060 : ℝ) / 65536) ((36917001597 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_023_2 <;> assumption
