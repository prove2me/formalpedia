-- Prove2me | solution 1 for RH1E6S06.part_028_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:24:36.807169+00:00
-- url     : https://prove2.me/submissions/585d6910-1cc0-445b-8bd6-c2800b548808

import Definitions.Def_RH1E6S06_D028_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0226 : RS5.BandZeros ((27280951542 : ℝ) / 65536) ((27285655352 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0226.s0 RH1E6S06_0226.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0226.s0 RH1E6S06_0226.rest = RH1E6S06_0226.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0226.s0 :: RH1E6S06_0226.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0226.s0.t = ((27280951542 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0226.s0]
  have e1 : RH1E6S06_0226.sL.t = ((27285655352 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0226.sL]
  rw [e0, e1] at h
  exact h

theorem band_0227 : RS5.BandZeros ((27285655352 : ℝ) / 65536) ((27290374464 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0227.s0 RH1E6S06_0227.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0227.s0 RH1E6S06_0227.rest = RH1E6S06_0227.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0227.s0 :: RH1E6S06_0227.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0227.s0.t = ((27285655352 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0227.s0]
  have e1 : RH1E6S06_0227.sL.t = ((27290374464 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0227.sL]
  rw [e0, e1] at h
  exact h

theorem part_028_1 : RS5.BandZeros ((27280951542 : ℝ) / 65536) ((27290374464 : ℝ) / 65536) 254 := by
  have g0 := band_0226
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0227
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27280951542 : ℝ) / 65536) ((27290374464 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_028_1 <;> assumption
