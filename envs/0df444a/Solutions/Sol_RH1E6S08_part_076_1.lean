-- Prove2me | solution 1 for RH1E6S08.part_076_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T07:33:25.411327+00:00
-- url     : https://prove2.me/submissions/ecf1cf08-94fa-4a5e-835a-cc645db2503d

import Definitions.Def_RH1E6S08_D076_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0610 : RS5.BandZeros ((35584506882 : ℝ) / 65536) ((35589099851 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0610.s0 RH1E6S08_0610.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0610.s0 RH1E6S08_0610.rest = RH1E6S08_0610.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0610.s0 :: RH1E6S08_0610.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0610.s0.t = ((35584506882 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0610.s0]
  have e1 : RH1E6S08_0610.sL.t = ((35589099851 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0610.sL]
  rw [e0, e1] at h
  exact h

theorem band_0611 : RS5.BandZeros ((35589099851 : ℝ) / 65536) ((35593701844 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0611.s0 RH1E6S08_0611.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0611.s0 RH1E6S08_0611.rest = RH1E6S08_0611.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0611.s0 :: RH1E6S08_0611.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0611.s0.t = ((35589099851 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0611.s0]
  have e1 : RH1E6S08_0611.sL.t = ((35593701844 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0611.sL]
  rw [e0, e1] at h
  exact h

theorem part_076_1 : RS5.BandZeros ((35584506882 : ℝ) / 65536) ((35593701844 : ℝ) / 65536) 254 := by
  have g0 := band_0610
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0611
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35584506882 : ℝ) / 65536) ((35593701844 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_076_1 <;> assumption
