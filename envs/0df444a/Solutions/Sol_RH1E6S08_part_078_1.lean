-- Prove2me | solution 1 for RH1E6S08.part_078_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T07:39:24.323315+00:00
-- url     : https://prove2.me/submissions/8c1a9652-4633-402f-84e2-8a0803a9182a

import Definitions.Def_RH1E6S08_D078_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0626 : RS5.BandZeros ((35658099526 : ℝ) / 65536) ((35662700938 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0626.s0 RH1E6S08_0626.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0626.s0 RH1E6S08_0626.rest = RH1E6S08_0626.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0626.s0 :: RH1E6S08_0626.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0626.s0.t = ((35658099526 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0626.s0]
  have e1 : RH1E6S08_0626.sL.t = ((35662700938 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0626.sL]
  rw [e0, e1] at h
  exact h

theorem band_0627 : RS5.BandZeros ((35662700938 : ℝ) / 65536) ((35667311959 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0627.s0 RH1E6S08_0627.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0627.s0 RH1E6S08_0627.rest = RH1E6S08_0627.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0627.s0 :: RH1E6S08_0627.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0627.s0.t = ((35662700938 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0627.s0]
  have e1 : RH1E6S08_0627.sL.t = ((35667311959 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0627.sL]
  rw [e0, e1] at h
  exact h

theorem part_078_1 : RS5.BandZeros ((35658099526 : ℝ) / 65536) ((35667311959 : ℝ) / 65536) 254 := by
  have g0 := band_0626
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0627
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35658099526 : ℝ) / 65536) ((35667311959 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_078_1 <;> assumption
