-- Prove2me | solution 1 for RH1E6S05.part_037_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T13:54:04.301991+00:00
-- url     : https://prove2.me/submissions/e642bf5b-6625-4568-ac26-1d16796c69ab

import Definitions.Def_RH1E6S05_D037_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0300 : RS5.BandZeros ((24369264675 : ℝ) / 65536) ((24374014430 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0300.s0 RH1E6S05_0300.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0300.s0 RH1E6S05_0300.rest = RH1E6S05_0300.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0300.s0 :: RH1E6S05_0300.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0300.s0.t = ((24369264675 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0300.s0]
  have e1 : RH1E6S05_0300.sL.t = ((24374014430 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0300.sL]
  rw [e0, e1] at h
  exact h

theorem band_0301 : RS5.BandZeros ((24374014430 : ℝ) / 65536) ((24378782836 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0301.s0 RH1E6S05_0301.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0301.s0 RH1E6S05_0301.rest = RH1E6S05_0301.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0301.s0 :: RH1E6S05_0301.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0301.s0.t = ((24374014430 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0301.s0]
  have e1 : RH1E6S05_0301.sL.t = ((24378782836 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0301.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_2 : RS5.BandZeros ((24369264675 : ℝ) / 65536) ((24378782836 : ℝ) / 65536) 254 := by
  have g0 := band_0300
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0301
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((24369264675 : ℝ) / 65536) ((24378782836 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_037_2 <;> assumption
