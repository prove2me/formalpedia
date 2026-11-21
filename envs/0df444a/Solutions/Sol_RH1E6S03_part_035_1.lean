-- Prove2me | solution 1 for RH1E6S03.part_035_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:32:53.980313+00:00
-- url     : https://prove2.me/submissions/abbde980-35f0-4c4d-816d-96c4e7c15506

import Definitions.Def_RH1E6S03_D035_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0282 : RS5.BandZeros ((17770994632 : ℝ) / 65536) ((17775884891 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0282.s0 RH1E6S03_0282.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0282.s0 RH1E6S03_0282.rest = RH1E6S03_0282.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0282.s0 :: RH1E6S03_0282.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0282.s0.t = ((17770994632 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0282.s0]
  have e1 : RH1E6S03_0282.sL.t = ((17775884891 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0282.sL]
  rw [e0, e1] at h
  exact h

theorem band_0283 : RS5.BandZeros ((17775884891 : ℝ) / 65536) ((17780784669 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0283.s0 RH1E6S03_0283.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0283.s0 RH1E6S03_0283.rest = RH1E6S03_0283.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0283.s0 :: RH1E6S03_0283.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0283.s0.t = ((17775884891 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0283.s0]
  have e1 : RH1E6S03_0283.sL.t = ((17780784669 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0283.sL]
  rw [e0, e1] at h
  exact h

theorem part_035_1 : RS5.BandZeros ((17770994632 : ℝ) / 65536) ((17780784669 : ℝ) / 65536) 254 := by
  have g0 := band_0282
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0283
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17770994632 : ℝ) / 65536) ((17780784669 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_035_1 <;> assumption
