-- Prove2me | solution 1 for RH1E6S15.part_079_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T12:51:24.230993+00:00
-- url     : https://prove2.me/submissions/f9b98fc1-8662-4692-b08f-f1e3211fc7d0

import Definitions.Def_RH1E6S15_D079_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0632 : RS5.BandZeros ((58497061687 : ℝ) / 65536) ((58501479702 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0632.s0 RH1E6S15_0632.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0632.s0 RH1E6S15_0632.rest = RH1E6S15_0632.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0632.s0 :: RH1E6S15_0632.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0632.s0.t = ((58497061687 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0632.s0]
  have e1 : RH1E6S15_0632.sL.t = ((58501479702 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0632.sL]
  rw [e0, e1] at h
  exact h

theorem band_0633 : RS5.BandZeros ((58501479702 : ℝ) / 65536) ((58505881815 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0633.s0 RH1E6S15_0633.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0633.s0 RH1E6S15_0633.rest = RH1E6S15_0633.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0633.s0 :: RH1E6S15_0633.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0633.s0.t = ((58501479702 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0633.s0]
  have e1 : RH1E6S15_0633.sL.t = ((58505881815 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0633.sL]
  rw [e0, e1] at h
  exact h

theorem part_079_0 : RS5.BandZeros ((58497061687 : ℝ) / 65536) ((58505881815 : ℝ) / 65536) 254 := by
  have g0 := band_0632
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0633
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58497061687 : ℝ) / 65536) ((58505881815 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_079_0 <;> assumption
