-- Prove2me | solution 1 for RH1E6S03.part_044_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:52:34.738839+00:00
-- url     : https://prove2.me/submissions/27ba49c0-8324-4084-b9fc-cba5515162df

import Definitions.Def_RH1E6S03_D044_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0354 : RS5.BandZeros ((18123466938 : ℝ) / 65536) ((18128357843 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0354.s0 RH1E6S03_0354.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0354.s0 RH1E6S03_0354.rest = RH1E6S03_0354.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0354.s0 :: RH1E6S03_0354.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0354.s0.t = ((18123466938 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0354.s0]
  have e1 : RH1E6S03_0354.sL.t = ((18128357843 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0354.sL]
  rw [e0, e1] at h
  exact h

theorem band_0355 : RS5.BandZeros ((18128357843 : ℝ) / 65536) ((18133248625 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0355.s0 RH1E6S03_0355.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0355.s0 RH1E6S03_0355.rest = RH1E6S03_0355.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0355.s0 :: RH1E6S03_0355.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0355.s0.t = ((18128357843 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0355.s0]
  have e1 : RH1E6S03_0355.sL.t = ((18133248625 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0355.sL]
  rw [e0, e1] at h
  exact h

theorem part_044_1 : RS5.BandZeros ((18123466938 : ℝ) / 65536) ((18133248625 : ℝ) / 65536) 254 := by
  have g0 := band_0354
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0355
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18123466938 : ℝ) / 65536) ((18133248625 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_044_1 <;> assumption
