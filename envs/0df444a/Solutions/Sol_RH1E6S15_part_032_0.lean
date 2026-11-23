-- Prove2me | solution 1 for RH1E6S15.part_032_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T09:44:52.251149+00:00
-- url     : https://prove2.me/submissions/5839050c-a00d-487c-940c-96a2a90f6062

import Definitions.Def_RH1E6S15_D032_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0256 : RS5.BandZeros ((56837683891 : ℝ) / 65536) ((56842116561 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0256.s0 RH1E6S15_0256.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0256.s0 RH1E6S15_0256.rest = RH1E6S15_0256.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0256.s0 :: RH1E6S15_0256.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0256.s0.t = ((56837683891 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0256.s0]
  have e1 : RH1E6S15_0256.sL.t = ((56842116561 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0256.sL]
  rw [e0, e1] at h
  exact h

theorem band_0257 : RS5.BandZeros ((56842116561 : ℝ) / 65536) ((56846526727 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0257.s0 RH1E6S15_0257.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0257.s0 RH1E6S15_0257.rest = RH1E6S15_0257.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0257.s0 :: RH1E6S15_0257.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0257.s0.t = ((56842116561 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0257.s0]
  have e1 : RH1E6S15_0257.sL.t = ((56846526727 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0257.sL]
  rw [e0, e1] at h
  exact h

theorem part_032_0 : RS5.BandZeros ((56837683891 : ℝ) / 65536) ((56846526727 : ℝ) / 65536) 254 := by
  have g0 := band_0256
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0257
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56837683891 : ℝ) / 65536) ((56846526727 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_032_0 <;> assumption
