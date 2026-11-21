-- Prove2me | solution 1 for RH1E6S06.part_070_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T21:48:29.063398+00:00
-- url     : https://prove2.me/submissions/333f7f4a-af3f-425f-9597-f6b984146524

import Definitions.Def_RH1E6S06_D070_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0560 : RS5.BandZeros ((28850360295 : ℝ) / 65536) ((28855059724 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0560.s0 RH1E6S06_0560.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0560.s0 RH1E6S06_0560.rest = RH1E6S06_0560.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0560.s0 :: RH1E6S06_0560.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0560.s0.t = ((28850360295 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0560.s0]
  have e1 : RH1E6S06_0560.sL.t = ((28855059724 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0560.sL]
  rw [e0, e1] at h
  exact h

theorem band_0561 : RS5.BandZeros ((28855059724 : ℝ) / 65536) ((28859737557 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0561.s0 RH1E6S06_0561.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0561.s0 RH1E6S06_0561.rest = RH1E6S06_0561.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0561.s0 :: RH1E6S06_0561.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0561.s0.t = ((28855059724 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0561.s0]
  have e1 : RH1E6S06_0561.sL.t = ((28859737557 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0561.sL]
  rw [e0, e1] at h
  exact h

theorem part_070_0 : RS5.BandZeros ((28850360295 : ℝ) / 65536) ((28859737557 : ℝ) / 65536) 254 := by
  have g0 := band_0560
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0561
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28850360295 : ℝ) / 65536) ((28859737557 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_070_0 <;> assumption
