-- Prove2me | solution 1 for RH1E6S16.part_002_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:59:44.953054+00:00
-- url     : https://prove2.me/submissions/d18fb5e5-a924-4396-9553-cfa253c1658b

import Definitions.Def_RH1E6S16_D002_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0020 : RS5.BandZeros ((59070484897 : ℝ) / 65536) ((59074883768 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0020.s0 RH1E6S16_0020.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0020.s0 RH1E6S16_0020.rest = RH1E6S16_0020.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0020.s0 :: RH1E6S16_0020.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0020.s0.t = ((59070484897 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0020.s0]
  have e1 : RH1E6S16_0020.sL.t = ((59074883768 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0020.sL]
  rw [e0, e1] at h
  exact h

theorem band_0021 : RS5.BandZeros ((59074883768 : ℝ) / 65536) ((59079298039 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0021.s0 RH1E6S16_0021.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0021.s0 RH1E6S16_0021.rest = RH1E6S16_0021.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0021.s0 :: RH1E6S16_0021.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0021.s0.t = ((59074883768 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0021.s0]
  have e1 : RH1E6S16_0021.sL.t = ((59079298039 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0021.sL]
  rw [e0, e1] at h
  exact h

theorem part_002_2 : RS5.BandZeros ((59070484897 : ℝ) / 65536) ((59079298039 : ℝ) / 65536) 254 := by
  have g0 := band_0020
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0021
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59070484897 : ℝ) / 65536) ((59079298039 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_002_2 <;> assumption
