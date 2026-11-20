-- Prove2me | solution 1 for RH1E6S02.part_048_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:49:15.086173+00:00
-- url     : https://prove2.me/submissions/d6e05e0c-da91-4027-a193-1d1ab86c16e2

import Definitions.Def_RH1E6S02_D048_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0384 : RS5.BandZeros ((15031033767 : ℝ) / 65536) ((15036023445 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0384.s0 RH1E6S02_0384.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0384.s0 RH1E6S02_0384.rest = RH1E6S02_0384.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0384.s0 :: RH1E6S02_0384.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0384.s0.t = ((15031033767 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0384.s0]
  have e1 : RH1E6S02_0384.sL.t = ((15036023445 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0384.sL]
  rw [e0, e1] at h
  exact h

theorem band_0385 : RS5.BandZeros ((15036023445 : ℝ) / 65536) ((15040995824 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0385.s0 RH1E6S02_0385.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0385.s0 RH1E6S02_0385.rest = RH1E6S02_0385.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0385.s0 :: RH1E6S02_0385.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0385.s0.t = ((15036023445 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0385.s0]
  have e1 : RH1E6S02_0385.sL.t = ((15040995824 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0385.sL]
  rw [e0, e1] at h
  exact h

theorem part_048_0 : RS5.BandZeros ((15031033767 : ℝ) / 65536) ((15040995824 : ℝ) / 65536) 254 := by
  have g0 := band_0384
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0385
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((15031033767 : ℝ) / 65536) ((15040995824 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_048_0 <;> assumption
