-- Prove2me | solution 1 for RH1E6S03.part_051_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T07:07:13.672184+00:00
-- url     : https://prove2.me/submissions/9aa59e79-d678-44c6-b4dd-adae8bac8c3c

import Definitions.Def_RH1E6S03_D051_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0408 : RS5.BandZeros ((18387390683 : ℝ) / 65536) ((18392284600 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0408.s0 RH1E6S03_0408.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0408.s0 RH1E6S03_0408.rest = RH1E6S03_0408.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0408.s0 :: RH1E6S03_0408.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0408.s0.t = ((18387390683 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0408.s0]
  have e1 : RH1E6S03_0408.sL.t = ((18392284600 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0408.sL]
  rw [e0, e1] at h
  exact h

theorem band_0409 : RS5.BandZeros ((18392284600 : ℝ) / 65536) ((18397168781 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0409.s0 RH1E6S03_0409.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0409.s0 RH1E6S03_0409.rest = RH1E6S03_0409.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0409.s0 :: RH1E6S03_0409.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0409.s0.t = ((18392284600 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0409.s0]
  have e1 : RH1E6S03_0409.sL.t = ((18397168781 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0409.sL]
  rw [e0, e1] at h
  exact h

theorem part_051_0 : RS5.BandZeros ((18387390683 : ℝ) / 65536) ((18397168781 : ℝ) / 65536) 254 := by
  have g0 := band_0408
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0409
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18387390683 : ℝ) / 65536) ((18397168781 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_051_0 <;> assumption
