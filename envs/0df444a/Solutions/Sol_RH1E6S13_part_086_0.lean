-- Prove2me | solution 1 for RH1E6S13.part_086_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:04:45.464532+00:00
-- url     : https://prove2.me/submissions/f1040f2e-8af1-4094-bf97-e2d916afb81f

import Definitions.Def_RH1E6S13_D086_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0688 : RS5.BandZeros ((52221754390 : ℝ) / 65536) ((52226222366 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0688.s0 RH1E6S13_0688.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0688.s0 RH1E6S13_0688.rest = RH1E6S13_0688.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0688.s0 :: RH1E6S13_0688.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0688.s0.t = ((52221754390 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0688.s0]
  have e1 : RH1E6S13_0688.sL.t = ((52226222366 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0688.sL]
  rw [e0, e1] at h
  exact h

theorem band_0689 : RS5.BandZeros ((52226222366 : ℝ) / 65536) ((52230655267 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0689.s0 RH1E6S13_0689.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0689.s0 RH1E6S13_0689.rest = RH1E6S13_0689.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0689.s0 :: RH1E6S13_0689.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0689.s0.t = ((52226222366 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0689.s0]
  have e1 : RH1E6S13_0689.sL.t = ((52230655267 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0689.sL]
  rw [e0, e1] at h
  exact h

theorem part_086_0 : RS5.BandZeros ((52221754390 : ℝ) / 65536) ((52230655267 : ℝ) / 65536) 254 := by
  have g0 := band_0688
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0689
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((52221754390 : ℝ) / 65536) ((52230655267 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_086_0 <;> assumption
