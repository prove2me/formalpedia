-- Prove2me | solution 1 for RH1E6S03.part_059_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T07:26:47.657773+00:00
-- url     : https://prove2.me/submissions/fdd69408-5548-440d-bc28-4ebf92af170b

import Definitions.Def_RH1E6S03_D059_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0472 : RS5.BandZeros ((18699733910 : ℝ) / 65536) ((18704610542 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0472.s0 RH1E6S03_0472.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0472.s0 RH1E6S03_0472.rest = RH1E6S03_0472.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0472.s0 :: RH1E6S03_0472.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0472.s0.t = ((18699733910 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0472.s0]
  have e1 : RH1E6S03_0472.sL.t = ((18704610542 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0472.sL]
  rw [e0, e1] at h
  exact h

theorem band_0473 : RS5.BandZeros ((18704610542 : ℝ) / 65536) ((18709496654 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0473.s0 RH1E6S03_0473.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0473.s0 RH1E6S03_0473.rest = RH1E6S03_0473.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0473.s0 :: RH1E6S03_0473.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0473.s0.t = ((18704610542 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0473.s0]
  have e1 : RH1E6S03_0473.sL.t = ((18709496654 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0473.sL]
  rw [e0, e1] at h
  exact h

theorem part_059_0 : RS5.BandZeros ((18699733910 : ℝ) / 65536) ((18709496654 : ℝ) / 65536) 254 := by
  have g0 := band_0472
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0473
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18699733910 : ℝ) / 65536) ((18709496654 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_059_0 <;> assumption
