-- Prove2me | solution 1 for RH1E6S03.part_053_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T07:12:13.031561+00:00
-- url     : https://prove2.me/submissions/79487d38-1f67-440c-a382-e60037158be5

import Definitions.Def_RH1E6S03_D053_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0426 : RS5.BandZeros ((18475289624 : ℝ) / 65536) ((18480181362 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0426.s0 RH1E6S03_0426.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0426.s0 RH1E6S03_0426.rest = RH1E6S03_0426.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0426.s0 :: RH1E6S03_0426.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0426.s0.t = ((18475289624 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0426.s0]
  have e1 : RH1E6S03_0426.sL.t = ((18480181362 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0426.sL]
  rw [e0, e1] at h
  exact h

theorem band_0427 : RS5.BandZeros ((18480181362 : ℝ) / 65536) ((18485072980 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0427.s0 RH1E6S03_0427.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0427.s0 RH1E6S03_0427.rest = RH1E6S03_0427.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0427.s0 :: RH1E6S03_0427.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0427.s0.t = ((18480181362 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0427.s0]
  have e1 : RH1E6S03_0427.sL.t = ((18485072980 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0427.sL]
  rw [e0, e1] at h
  exact h

theorem part_053_1 : RS5.BandZeros ((18475289624 : ℝ) / 65536) ((18485072980 : ℝ) / 65536) 254 := by
  have g0 := band_0426
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0427
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18475289624 : ℝ) / 65536) ((18485072980 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_053_1 <;> assumption
