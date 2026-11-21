-- Prove2me | solution 1 for RH1E6S06.part_001_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:17:33.031157+00:00
-- url     : https://prove2.me/submissions/ea8ffaa7-e7a4-47a6-a8fa-376d42e1495c

import Definitions.Def_RH1E6S06_D001_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0012 : RS5.BandZeros ((26271130920 : ℝ) / 65536) ((26275848745 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0012.s0 RH1E6S06_0012.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0012.s0 RH1E6S06_0012.rest = RH1E6S06_0012.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0012.s0 :: RH1E6S06_0012.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0012.s0.t = ((26271130920 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0012.s0]
  have e1 : RH1E6S06_0012.sL.t = ((26275848745 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0012.sL]
  rw [e0, e1] at h
  exact h

theorem band_0013 : RS5.BandZeros ((26275848745 : ℝ) / 65536) ((26280592014 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0013.s0 RH1E6S06_0013.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0013.s0 RH1E6S06_0013.rest = RH1E6S06_0013.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0013.s0 :: RH1E6S06_0013.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0013.s0.t = ((26275848745 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0013.s0]
  have e1 : RH1E6S06_0013.sL.t = ((26280592014 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0013.sL]
  rw [e0, e1] at h
  exact h

theorem part_001_2 : RS5.BandZeros ((26271130920 : ℝ) / 65536) ((26280592014 : ℝ) / 65536) 254 := by
  have g0 := band_0012
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0013
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((26271130920 : ℝ) / 65536) ((26280592014 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_001_2 <;> assumption
