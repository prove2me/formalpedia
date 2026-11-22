-- Prove2me | solution 1 for RH1E6S08.part_069_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T07:16:35.288608+00:00
-- url     : https://prove2.me/submissions/00252cee-5699-44d5-9109-48049140aa7d

import Definitions.Def_RH1E6S08_D069_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0558 : RS5.BandZeros ((35345202959 : ℝ) / 65536) ((35349799641 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0558.s0 RH1E6S08_0558.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0558.s0 RH1E6S08_0558.rest = RH1E6S08_0558.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0558.s0 :: RH1E6S08_0558.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0558.s0.t = ((35345202959 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0558.s0]
  have e1 : RH1E6S08_0558.sL.t = ((35349799641 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0558.sL]
  rw [e0, e1] at h
  exact h

theorem band_0559 : RS5.BandZeros ((35349799641 : ℝ) / 65536) ((35354408782 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0559.s0 RH1E6S08_0559.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0559.s0 RH1E6S08_0559.rest = RH1E6S08_0559.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0559.s0 :: RH1E6S08_0559.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0559.s0.t = ((35349799641 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0559.s0]
  have e1 : RH1E6S08_0559.sL.t = ((35354408782 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0559.sL]
  rw [e0, e1] at h
  exact h

theorem part_069_3 : RS5.BandZeros ((35345202959 : ℝ) / 65536) ((35354408782 : ℝ) / 65536) 254 := by
  have g0 := band_0558
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0559
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35345202959 : ℝ) / 65536) ((35354408782 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_069_3 <;> assumption
