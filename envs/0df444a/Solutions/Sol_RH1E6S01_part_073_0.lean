-- Prove2me | solution 1 for RH1E6S01.part_073_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:51:28.951079+00:00
-- url     : https://prove2.me/submissions/fcd755d5-b1f0-4ed9-9cdd-bf83b5a9b6b3

import Definitions.Def_RH1E6S01_D073_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0584 : RS5.BandZeros ((12818964825 : ℝ) / 65536) ((12824019398 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0584.s0 RH1E6S01_0584.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0584.s0 RH1E6S01_0584.rest = RH1E6S01_0584.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0584.s0 :: RH1E6S01_0584.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0584.s0.t = ((12818964825 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0584.s0]
  have e1 : RH1E6S01_0584.sL.t = ((12824019398 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0584.sL]
  rw [e0, e1] at h
  exact h

theorem band_0585 : RS5.BandZeros ((12824019398 : ℝ) / 65536) ((12829063829 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0585.s0 RH1E6S01_0585.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0585.s0 RH1E6S01_0585.rest = RH1E6S01_0585.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0585.s0 :: RH1E6S01_0585.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0585.s0.t = ((12824019398 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0585.s0]
  have e1 : RH1E6S01_0585.sL.t = ((12829063829 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0585.sL]
  rw [e0, e1] at h
  exact h

theorem part_073_0 : RS5.BandZeros ((12818964825 : ℝ) / 65536) ((12829063829 : ℝ) / 65536) 254 := by
  have g0 := band_0584
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0585
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12818964825 : ℝ) / 65536) ((12829063829 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_073_0 <;> assumption
