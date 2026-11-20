-- Prove2me | solution 1 for RH1E6S01.part_031_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:24:35.582942+00:00
-- url     : https://prove2.me/submissions/b0f5e94c-5d38-47dc-84e8-762339db194d

import Definitions.Def_RH1E6S01_D031_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0250 : RS5.BandZeros ((11119318273 : ℝ) / 65536) ((11124413024 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0250.s0 RH1E6S01_0250.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0250.s0 RH1E6S01_0250.rest = RH1E6S01_0250.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0250.s0 :: RH1E6S01_0250.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0250.s0.t = ((11119318273 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0250.s0]
  have e1 : RH1E6S01_0250.sL.t = ((11124413024 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0250.sL]
  rw [e0, e1] at h
  exact h

theorem band_0251 : RS5.BandZeros ((11124413024 : ℝ) / 65536) ((11129547899 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0251.s0 RH1E6S01_0251.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0251.s0 RH1E6S01_0251.rest = RH1E6S01_0251.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0251.s0 :: RH1E6S01_0251.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0251.s0.t = ((11124413024 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0251.s0]
  have e1 : RH1E6S01_0251.sL.t = ((11129547899 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0251.sL]
  rw [e0, e1] at h
  exact h

theorem part_031_1 : RS5.BandZeros ((11119318273 : ℝ) / 65536) ((11129547899 : ℝ) / 65536) 254 := by
  have g0 := band_0250
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0251
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11119318273 : ℝ) / 65536) ((11129547899 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_031_1 <;> assumption
