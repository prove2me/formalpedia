-- Prove2me | solution 1 for RH1E6S03.part_060_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T07:29:22.188368+00:00
-- url     : https://prove2.me/submissions/f7322644-3fbe-4ad4-bb9a-2e29e91bc004

import Definitions.Def_RH1E6S03_D060_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0486 : RS5.BandZeros ((18768015169 : ℝ) / 65536) ((18772880548 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0486.s0 RH1E6S03_0486.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0486.s0 RH1E6S03_0486.rest = RH1E6S03_0486.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0486.s0 :: RH1E6S03_0486.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0486.s0.t = ((18768015169 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0486.s0]
  have e1 : RH1E6S03_0486.sL.t = ((18772880548 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0486.sL]
  rw [e0, e1] at h
  exact h

theorem band_0487 : RS5.BandZeros ((18772880548 : ℝ) / 65536) ((18777755405 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0487.s0 RH1E6S03_0487.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0487.s0 RH1E6S03_0487.rest = RH1E6S03_0487.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0487.s0 :: RH1E6S03_0487.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0487.s0.t = ((18772880548 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0487.s0]
  have e1 : RH1E6S03_0487.sL.t = ((18777755405 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0487.sL]
  rw [e0, e1] at h
  exact h

theorem part_060_3 : RS5.BandZeros ((18768015169 : ℝ) / 65536) ((18777755405 : ℝ) / 65536) 254 := by
  have g0 := band_0486
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0487
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18768015169 : ℝ) / 65536) ((18777755405 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_060_3 <;> assumption
