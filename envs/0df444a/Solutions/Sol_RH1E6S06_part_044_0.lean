-- Prove2me | solution 1 for RH1E6S06.part_044_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T19:07:01.902281+00:00
-- url     : https://prove2.me/submissions/6e523725-f563-41ed-882f-68ffc3e93f78

import Definitions.Def_RH1E6S06_D044_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0352 : RS5.BandZeros ((27873920868 : ℝ) / 65536) ((27878623846 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0352.s0 RH1E6S06_0352.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0352.s0 RH1E6S06_0352.rest = RH1E6S06_0352.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0352.s0 :: RH1E6S06_0352.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0352.s0.t = ((27873920868 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0352.s0]
  have e1 : RH1E6S06_0352.sL.t = ((27878623846 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0352.sL]
  rw [e0, e1] at h
  exact h

theorem band_0353 : RS5.BandZeros ((27878623846 : ℝ) / 65536) ((27883335749 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0353.s0 RH1E6S06_0353.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0353.s0 RH1E6S06_0353.rest = RH1E6S06_0353.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0353.s0 :: RH1E6S06_0353.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0353.s0.t = ((27878623846 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0353.s0]
  have e1 : RH1E6S06_0353.sL.t = ((27883335749 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0353.sL]
  rw [e0, e1] at h
  exact h

theorem part_044_0 : RS5.BandZeros ((27873920868 : ℝ) / 65536) ((27883335749 : ℝ) / 65536) 254 := by
  have g0 := band_0352
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0353
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27873920868 : ℝ) / 65536) ((27883335749 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_044_0 <;> assumption
