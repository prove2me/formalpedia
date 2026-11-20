-- Prove2me | solution 1 for RH1E6S01.part_050_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:04:41.731226+00:00
-- url     : https://prove2.me/submissions/cfb7eb5b-0c0b-4374-9233-356b8f229864

import Definitions.Def_RH1E6S01_D050_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0400 : RS5.BandZeros ((11885558184 : ℝ) / 65536) ((11890629909 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0400.s0 RH1E6S01_0400.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0400.s0 RH1E6S01_0400.rest = RH1E6S01_0400.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0400.s0 :: RH1E6S01_0400.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0400.s0.t = ((11885558184 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0400.s0]
  have e1 : RH1E6S01_0400.sL.t = ((11890629909 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0400.sL]
  rw [e0, e1] at h
  exact h

theorem band_0401 : RS5.BandZeros ((11890629909 : ℝ) / 65536) ((11895721469 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0401.s0 RH1E6S01_0401.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0401.s0 RH1E6S01_0401.rest = RH1E6S01_0401.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0401.s0 :: RH1E6S01_0401.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0401.s0.t = ((11890629909 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0401.s0]
  have e1 : RH1E6S01_0401.sL.t = ((11895721469 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0401.sL]
  rw [e0, e1] at h
  exact h

theorem part_050_0 : RS5.BandZeros ((11885558184 : ℝ) / 65536) ((11895721469 : ℝ) / 65536) 254 := by
  have g0 := band_0400
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0401
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11885558184 : ℝ) / 65536) ((11895721469 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_050_0 <;> assumption
