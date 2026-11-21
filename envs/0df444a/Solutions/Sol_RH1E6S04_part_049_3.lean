-- Prove2me | solution 1 for RH1E6S04.part_049_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:15:24.089136+00:00
-- url     : https://prove2.me/submissions/56abc66d-8dd3-4a93-8aef-b3dd23d4a50b

import Definitions.Def_RH1E6S04_D049_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0398 : RS5.BandZeros ((21584240370 : ℝ) / 65536) ((21589052635 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0398.s0 RH1E6S04_0398.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0398.s0 RH1E6S04_0398.rest = RH1E6S04_0398.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0398.s0 :: RH1E6S04_0398.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0398.s0.t = ((21584240370 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0398.s0]
  have e1 : RH1E6S04_0398.sL.t = ((21589052635 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0398.sL]
  rw [e0, e1] at h
  exact h

theorem band_0399 : RS5.BandZeros ((21589052635 : ℝ) / 65536) ((21593883746 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0399.s0 RH1E6S04_0399.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0399.s0 RH1E6S04_0399.rest = RH1E6S04_0399.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0399.s0 :: RH1E6S04_0399.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0399.s0.t = ((21589052635 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0399.s0]
  have e1 : RH1E6S04_0399.sL.t = ((21593883746 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0399.sL]
  rw [e0, e1] at h
  exact h

theorem part_049_3 : RS5.BandZeros ((21584240370 : ℝ) / 65536) ((21593883746 : ℝ) / 65536) 254 := by
  have g0 := band_0398
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0399
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((21584240370 : ℝ) / 65536) ((21593883746 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_049_3 <;> assumption
