-- Prove2me | solution 1 for RH1E6S15.part_067_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T12:00:51.825461+00:00
-- url     : https://prove2.me/submissions/0734848e-0afc-4c79-9a1d-89077ffbccbf

import Definitions.Def_RH1E6S15_D067_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0542 : RS5.BandZeros ((58100249798 : ℝ) / 65536) ((58104646480 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0542.s0 RH1E6S15_0542.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0542.s0 RH1E6S15_0542.rest = RH1E6S15_0542.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0542.s0 :: RH1E6S15_0542.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0542.s0.t = ((58100249798 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0542.s0]
  have e1 : RH1E6S15_0542.sL.t = ((58104646480 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0542.sL]
  rw [e0, e1] at h
  exact h

theorem band_0543 : RS5.BandZeros ((58104646480 : ℝ) / 65536) ((58109053244 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0543.s0 RH1E6S15_0543.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0543.s0 RH1E6S15_0543.rest = RH1E6S15_0543.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0543.s0 :: RH1E6S15_0543.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0543.s0.t = ((58104646480 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0543.s0]
  have e1 : RH1E6S15_0543.sL.t = ((58109053244 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0543.sL]
  rw [e0, e1] at h
  exact h

theorem part_067_3 : RS5.BandZeros ((58100249798 : ℝ) / 65536) ((58109053244 : ℝ) / 65536) 254 := by
  have g0 := band_0542
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0543
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58100249798 : ℝ) / 65536) ((58109053244 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_067_3 <;> assumption
