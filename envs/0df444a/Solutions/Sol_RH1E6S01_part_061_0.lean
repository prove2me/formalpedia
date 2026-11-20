-- Prove2me | solution 1 for RH1E6S01.part_061_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:27:31.954754+00:00
-- url     : https://prove2.me/submissions/9dc29806-7b00-43f4-8dea-be6193032c39

import Definitions.Def_RH1E6S01_D061_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0488 : RS5.BandZeros ((12332814074 : ℝ) / 65536) ((12337887602 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0488.s0 RH1E6S01_0488.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0488.s0 RH1E6S01_0488.rest = RH1E6S01_0488.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0488.s0 :: RH1E6S01_0488.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0488.s0.t = ((12332814074 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0488.s0]
  have e1 : RH1E6S01_0488.sL.t = ((12337887602 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0488.sL]
  rw [e0, e1] at h
  exact h

theorem band_0489 : RS5.BandZeros ((12337887602 : ℝ) / 65536) ((12342960927 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0489.s0 RH1E6S01_0489.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0489.s0 RH1E6S01_0489.rest = RH1E6S01_0489.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0489.s0 :: RH1E6S01_0489.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0489.s0.t = ((12337887602 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0489.s0]
  have e1 : RH1E6S01_0489.sL.t = ((12342960927 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0489.sL]
  rw [e0, e1] at h
  exact h

theorem part_061_0 : RS5.BandZeros ((12332814074 : ℝ) / 65536) ((12342960927 : ℝ) / 65536) 254 := by
  have g0 := band_0488
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0489
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12332814074 : ℝ) / 65536) ((12342960927 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_061_0 <;> assumption
