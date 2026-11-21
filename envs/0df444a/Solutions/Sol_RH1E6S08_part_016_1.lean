-- Prove2me | solution 1 for RH1E6S08.part_016_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:40:17.91488+00:00
-- url     : https://prove2.me/submissions/8ac4d801-6430-4455-9989-56763d319ce1

import Definitions.Def_RH1E6S08_D016_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0130 : RS5.BandZeros ((33369994431 : ℝ) / 65536) ((33374630321 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0130.s0 RH1E6S08_0130.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0130.s0 RH1E6S08_0130.rest = RH1E6S08_0130.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0130.s0 :: RH1E6S08_0130.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0130.s0.t = ((33369994431 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0130.s0]
  have e1 : RH1E6S08_0130.sL.t = ((33374630321 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0130.sL]
  rw [e0, e1] at h
  exact h

theorem band_0131 : RS5.BandZeros ((33374630321 : ℝ) / 65536) ((33379238830 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0131.s0 RH1E6S08_0131.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0131.s0 RH1E6S08_0131.rest = RH1E6S08_0131.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0131.s0 :: RH1E6S08_0131.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0131.s0.t = ((33374630321 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0131.s0]
  have e1 : RH1E6S08_0131.sL.t = ((33379238830 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0131.sL]
  rw [e0, e1] at h
  exact h

theorem part_016_1 : RS5.BandZeros ((33369994431 : ℝ) / 65536) ((33379238830 : ℝ) / 65536) 254 := by
  have g0 := band_0130
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0131
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33369994431 : ℝ) / 65536) ((33379238830 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_016_1 <;> assumption
