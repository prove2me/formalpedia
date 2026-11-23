-- Prove2me | solution 1 for RH1E6S15.part_042_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:17:49.508626+00:00
-- url     : https://prove2.me/submissions/b4d989f7-cc27-4396-8c63-55d73adff2b1

import Definitions.Def_RH1E6S15_D042_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0336 : RS5.BandZeros ((57191080144 : ℝ) / 65536) ((57195517121 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0336.s0 RH1E6S15_0336.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0336.s0 RH1E6S15_0336.rest = RH1E6S15_0336.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0336.s0 :: RH1E6S15_0336.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0336.s0.t = ((57191080144 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0336.s0]
  have e1 : RH1E6S15_0336.sL.t = ((57195517121 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0336.sL]
  rw [e0, e1] at h
  exact h

theorem band_0337 : RS5.BandZeros ((57195517121 : ℝ) / 65536) ((57199916656 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0337.s0 RH1E6S15_0337.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0337.s0 RH1E6S15_0337.rest = RH1E6S15_0337.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0337.s0 :: RH1E6S15_0337.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0337.s0.t = ((57195517121 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0337.s0]
  have e1 : RH1E6S15_0337.sL.t = ((57199916656 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0337.sL]
  rw [e0, e1] at h
  exact h

theorem part_042_0 : RS5.BandZeros ((57191080144 : ℝ) / 65536) ((57199916656 : ℝ) / 65536) 254 := by
  have g0 := band_0336
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0337
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57191080144 : ℝ) / 65536) ((57199916656 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_042_0 <;> assumption
