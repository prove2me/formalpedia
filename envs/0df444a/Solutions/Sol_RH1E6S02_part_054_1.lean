-- Prove2me | solution 1 for RH1E6S02.part_054_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T04:03:47.065057+00:00
-- url     : https://prove2.me/submissions/60dc1801-f2a5-42ee-b0ee-3e106657697f

import Definitions.Def_RH1E6S02_D054_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0434 : RS5.BandZeros ((15279750295 : ℝ) / 65536) ((15284715343 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0434.s0 RH1E6S02_0434.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0434.s0 RH1E6S02_0434.rest = RH1E6S02_0434.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0434.s0 :: RH1E6S02_0434.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0434.s0.t = ((15279750295 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0434.s0]
  have e1 : RH1E6S02_0434.sL.t = ((15284715343 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0434.sL]
  rw [e0, e1] at h
  exact h

theorem band_0435 : RS5.BandZeros ((15284715343 : ℝ) / 65536) ((15289678627 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0435.s0 RH1E6S02_0435.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0435.s0 RH1E6S02_0435.rest = RH1E6S02_0435.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0435.s0 :: RH1E6S02_0435.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0435.s0.t = ((15284715343 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0435.s0]
  have e1 : RH1E6S02_0435.sL.t = ((15289678627 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0435.sL]
  rw [e0, e1] at h
  exact h

theorem part_054_1 : RS5.BandZeros ((15279750295 : ℝ) / 65536) ((15289678627 : ℝ) / 65536) 254 := by
  have g0 := band_0434
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0435
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((15279750295 : ℝ) / 65536) ((15289678627 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_054_1 <;> assumption
