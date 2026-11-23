-- Prove2me | solution 1 for RH1E6S15.part_004_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:58:57.35406+00:00
-- url     : https://prove2.me/submissions/9136af91-2205-4d4b-9cb0-a519d7558096

import Definitions.Def_RH1E6S15_D004_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0034 : RS5.BandZeros ((55856041679 : ℝ) / 65536) ((55860457622 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0034.s0 RH1E6S15_0034.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0034.s0 RH1E6S15_0034.rest = RH1E6S15_0034.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0034.s0 :: RH1E6S15_0034.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0034.s0.t = ((55856041679 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0034.s0]
  have e1 : RH1E6S15_0034.sL.t = ((55860457622 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0034.sL]
  rw [e0, e1] at h
  exact h

theorem band_0035 : RS5.BandZeros ((55860457622 : ℝ) / 65536) ((55864896420 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0035.s0 RH1E6S15_0035.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0035.s0 RH1E6S15_0035.rest = RH1E6S15_0035.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0035.s0 :: RH1E6S15_0035.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0035.s0.t = ((55860457622 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0035.s0]
  have e1 : RH1E6S15_0035.sL.t = ((55864896420 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0035.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_1 : RS5.BandZeros ((55856041679 : ℝ) / 65536) ((55864896420 : ℝ) / 65536) 254 := by
  have g0 := band_0034
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0035
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((55856041679 : ℝ) / 65536) ((55864896420 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_004_1 <;> assumption
