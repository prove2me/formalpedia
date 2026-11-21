-- Prove2me | solution 1 for RH1E6S06.part_043_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T19:04:18.831463+00:00
-- url     : https://prove2.me/submissions/e8de79d5-0183-4cb0-a186-c2612a6ac8ae

import Definitions.Def_RH1E6S06_D043_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0344 : RS5.BandZeros ((27836324944 : ℝ) / 65536) ((27841019925 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0344.s0 RH1E6S06_0344.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0344.s0 RH1E6S06_0344.rest = RH1E6S06_0344.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0344.s0 :: RH1E6S06_0344.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0344.s0.t = ((27836324944 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0344.s0]
  have e1 : RH1E6S06_0344.sL.t = ((27841019925 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0344.sL]
  rw [e0, e1] at h
  exact h

theorem band_0345 : RS5.BandZeros ((27841019925 : ℝ) / 65536) ((27845733581 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0345.s0 RH1E6S06_0345.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0345.s0 RH1E6S06_0345.rest = RH1E6S06_0345.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0345.s0 :: RH1E6S06_0345.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0345.s0.t = ((27841019925 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0345.s0]
  have e1 : RH1E6S06_0345.sL.t = ((27845733581 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0345.sL]
  rw [e0, e1] at h
  exact h

theorem part_043_0 : RS5.BandZeros ((27836324944 : ℝ) / 65536) ((27845733581 : ℝ) / 65536) 254 := by
  have g0 := band_0344
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0345
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27836324944 : ℝ) / 65536) ((27845733581 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_043_0 <;> assumption
