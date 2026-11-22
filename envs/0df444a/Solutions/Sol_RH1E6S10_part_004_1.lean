-- Prove2me | solution 1 for RH1E6S10.part_004_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T17:17:04.555898+00:00
-- url     : https://prove2.me/submissions/d8f6aebd-f8e8-4f9f-b7f8-3fd5f186ac9c

import Definitions.Def_RH1E6S10_D004_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0034 : RS5.BandZeros ((39476654916 : ℝ) / 65536) ((39481213918 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0034.s0 RH1E6S10_0034.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0034.s0 RH1E6S10_0034.rest = RH1E6S10_0034.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0034.s0 :: RH1E6S10_0034.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0034.s0.t = ((39476654916 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0034.s0]
  have e1 : RH1E6S10_0034.sL.t = ((39481213918 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0034.sL]
  rw [e0, e1] at h
  exact h

theorem band_0035 : RS5.BandZeros ((39481213918 : ℝ) / 65536) ((39485763900 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0035.s0 RH1E6S10_0035.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0035.s0 RH1E6S10_0035.rest = RH1E6S10_0035.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0035.s0 :: RH1E6S10_0035.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0035.s0.t = ((39481213918 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0035.s0]
  have e1 : RH1E6S10_0035.sL.t = ((39485763900 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0035.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_1 : RS5.BandZeros ((39476654916 : ℝ) / 65536) ((39485763900 : ℝ) / 65536) 254 := by
  have g0 := band_0034
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0035
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39476654916 : ℝ) / 65536) ((39485763900 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_004_1 <;> assumption
