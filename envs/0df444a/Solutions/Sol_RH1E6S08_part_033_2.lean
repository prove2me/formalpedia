-- Prove2me | solution 1 for RH1E6S08.part_033_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T05:27:46.188978+00:00
-- url     : https://prove2.me/submissions/48c2ee22-5d9e-438c-aa16-9a95d7acb456

import Definitions.Def_RH1E6S08_D033_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0268 : RS5.BandZeros ((34007970842 : ℝ) / 65536) ((34012574152 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0268.s0 RH1E6S08_0268.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0268.s0 RH1E6S08_0268.rest = RH1E6S08_0268.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0268.s0 :: RH1E6S08_0268.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0268.s0.t = ((34007970842 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0268.s0]
  have e1 : RH1E6S08_0268.sL.t = ((34012574152 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0268.sL]
  rw [e0, e1] at h
  exact h

theorem band_0269 : RS5.BandZeros ((34012574152 : ℝ) / 65536) ((34017185136 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0269.s0 RH1E6S08_0269.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0269.s0 RH1E6S08_0269.rest = RH1E6S08_0269.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0269.s0 :: RH1E6S08_0269.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0269.s0.t = ((34012574152 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0269.s0]
  have e1 : RH1E6S08_0269.sL.t = ((34017185136 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0269.sL]
  rw [e0, e1] at h
  exact h

theorem part_033_2 : RS5.BandZeros ((34007970842 : ℝ) / 65536) ((34017185136 : ℝ) / 65536) 254 := by
  have g0 := band_0268
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0269
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((34007970842 : ℝ) / 65536) ((34017185136 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_033_2 <;> assumption
