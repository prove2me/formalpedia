-- Prove2me | solution 1 for RH1E6S17.part_045_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:10:11.353218+00:00
-- url     : https://prove2.me/submissions/c1cdac14-3d48-4493-844e-7af438318c55

import Definitions.Def_RH1E6S17_D045_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0366 : RS5.BandZeros ((63862366536 : ℝ) / 65536) ((63866716222 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0366.s0 RH1E6S17_0366.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0366.s0 RH1E6S17_0366.rest = RH1E6S17_0366.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0366.s0 :: RH1E6S17_0366.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0366.s0.t = ((63862366536 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0366.s0]
  have e1 : RH1E6S17_0366.sL.t = ((63866716222 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0366.sL]
  rw [e0, e1] at h
  exact h

theorem band_0367 : RS5.BandZeros ((63866716222 : ℝ) / 65536) ((63871091723 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0367.s0 RH1E6S17_0367.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0367.s0 RH1E6S17_0367.rest = RH1E6S17_0367.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0367.s0 :: RH1E6S17_0367.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0367.s0.t = ((63866716222 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0367.s0]
  have e1 : RH1E6S17_0367.sL.t = ((63871091723 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0367.sL]
  rw [e0, e1] at h
  exact h

theorem part_045_3 : RS5.BandZeros ((63862366536 : ℝ) / 65536) ((63871091723 : ℝ) / 65536) 254 := by
  have g0 := band_0366
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0367
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63862366536 : ℝ) / 65536) ((63871091723 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_045_3 <;> assumption
