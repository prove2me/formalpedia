-- Prove2me | solution 1 for RH1E6S04.part_039_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:52:54.481946+00:00
-- url     : https://prove2.me/submissions/637a30b8-343a-4d2b-b49f-1cd1ce2fc79a

import Definitions.Def_RH1E6S04_D039_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0316 : RS5.BandZeros ((21189296070 : ℝ) / 65536) ((21194116525 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0316.s0 RH1E6S04_0316.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0316.s0 RH1E6S04_0316.rest = RH1E6S04_0316.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0316.s0 :: RH1E6S04_0316.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0316.s0.t = ((21189296070 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0316.s0]
  have e1 : RH1E6S04_0316.sL.t = ((21194116525 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0316.sL]
  rw [e0, e1] at h
  exact h

theorem band_0317 : RS5.BandZeros ((21194116525 : ℝ) / 65536) ((21198936880 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0317.s0 RH1E6S04_0317.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0317.s0 RH1E6S04_0317.rest = RH1E6S04_0317.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0317.s0 :: RH1E6S04_0317.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0317.s0.t = ((21194116525 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0317.s0]
  have e1 : RH1E6S04_0317.sL.t = ((21198936880 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0317.sL]
  rw [e0, e1] at h
  exact h

theorem part_039_2 : RS5.BandZeros ((21189296070 : ℝ) / 65536) ((21198936880 : ℝ) / 65536) 254 := by
  have g0 := band_0316
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0317
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((21189296070 : ℝ) / 65536) ((21198936880 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_039_2 <;> assumption
