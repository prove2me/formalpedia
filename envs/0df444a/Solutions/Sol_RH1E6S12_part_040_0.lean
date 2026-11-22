-- Prove2me | solution 1 for RH1E6S12.part_040_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T09:20:54.625725+00:00
-- url     : https://prove2.me/submissions/a864b85d-cad1-4710-ad1d-d1533dee64ef

import Definitions.Def_RH1E6S12_D040_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0320 : RS5.BandZeros ((47313330070 : ℝ) / 65536) ((47317810099 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0320.s0 RH1E6S12_0320.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0320.s0 RH1E6S12_0320.rest = RH1E6S12_0320.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0320.s0 :: RH1E6S12_0320.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0320.s0.t = ((47313330070 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0320.s0]
  have e1 : RH1E6S12_0320.sL.t = ((47317810099 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0320.sL]
  rw [e0, e1] at h
  exact h

theorem band_0321 : RS5.BandZeros ((47317810099 : ℝ) / 65536) ((47322304599 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0321.s0 RH1E6S12_0321.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0321.s0 RH1E6S12_0321.rest = RH1E6S12_0321.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0321.s0 :: RH1E6S12_0321.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0321.s0.t = ((47317810099 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0321.s0]
  have e1 : RH1E6S12_0321.sL.t = ((47322304599 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0321.sL]
  rw [e0, e1] at h
  exact h

theorem part_040_0 : RS5.BandZeros ((47313330070 : ℝ) / 65536) ((47322304599 : ℝ) / 65536) 254 := by
  have g0 := band_0320
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0321
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47313330070 : ℝ) / 65536) ((47322304599 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_040_0 <;> assumption
