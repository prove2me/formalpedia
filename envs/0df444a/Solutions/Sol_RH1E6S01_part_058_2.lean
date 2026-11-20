-- Prove2me | solution 1 for RH1E6S01.part_058_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:22:46.620687+00:00
-- url     : https://prove2.me/submissions/41c92f18-cb24-4192-94fb-e684062a4b5d

import Definitions.Def_RH1E6S01_D058_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0468 : RS5.BandZeros ((12231310843 : ℝ) / 65536) ((12236378446 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0468.s0 RH1E6S01_0468.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0468.s0 RH1E6S01_0468.rest = RH1E6S01_0468.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0468.s0 :: RH1E6S01_0468.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0468.s0.t = ((12231310843 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0468.s0]
  have e1 : RH1E6S01_0468.sL.t = ((12236378446 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0468.sL]
  rw [e0, e1] at h
  exact h

theorem band_0469 : RS5.BandZeros ((12236378446 : ℝ) / 65536) ((12241475830 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0469.s0 RH1E6S01_0469.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0469.s0 RH1E6S01_0469.rest = RH1E6S01_0469.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0469.s0 :: RH1E6S01_0469.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0469.s0.t = ((12236378446 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0469.s0]
  have e1 : RH1E6S01_0469.sL.t = ((12241475830 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0469.sL]
  rw [e0, e1] at h
  exact h

theorem part_058_2 : RS5.BandZeros ((12231310843 : ℝ) / 65536) ((12241475830 : ℝ) / 65536) 254 := by
  have g0 := band_0468
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0469
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12231310843 : ℝ) / 65536) ((12241475830 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_058_2 <;> assumption
