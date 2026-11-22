-- Prove2me | solution 1 for RH1E6S09.part_004_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T08:22:21.083316+00:00
-- url     : https://prove2.me/submissions/91ca24d1-60ac-4738-9948-07352630ee5f

import Definitions.Def_RH1E6S09_D004_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0034 : RS5.BandZeros ((36200984086 : ℝ) / 65536) ((36205586818 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0034.s0 RH1E6S09_0034.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0034.s0 RH1E6S09_0034.rest = RH1E6S09_0034.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0034.s0 :: RH1E6S09_0034.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0034.s0.t = ((36200984086 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0034.s0]
  have e1 : RH1E6S09_0034.sL.t = ((36205586818 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0034.sL]
  rw [e0, e1] at h
  exact h

theorem band_0035 : RS5.BandZeros ((36205586818 : ℝ) / 65536) ((36210185219 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0035.s0 RH1E6S09_0035.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0035.s0 RH1E6S09_0035.rest = RH1E6S09_0035.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0035.s0 :: RH1E6S09_0035.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0035.s0.t = ((36205586818 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0035.s0]
  have e1 : RH1E6S09_0035.sL.t = ((36210185219 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0035.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_1 : RS5.BandZeros ((36200984086 : ℝ) / 65536) ((36210185219 : ℝ) / 65536) 254 := by
  have g0 := band_0034
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0035
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36200984086 : ℝ) / 65536) ((36210185219 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_004_1 <;> assumption
