-- Prove2me | solution 1 for RH1E6S01.part_019_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:00:57.505085+00:00
-- url     : https://prove2.me/submissions/1ee0092a-d834-464a-962e-b0ad26c8d7d3

import Definitions.Def_RH1E6S01_D019_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0154 : RS5.BandZeros ((10626197577 : ℝ) / 65536) ((10631345473 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0154.s0 RH1E6S01_0154.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0154.s0 RH1E6S01_0154.rest = RH1E6S01_0154.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0154.s0 :: RH1E6S01_0154.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0154.s0.t = ((10626197577 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0154.s0]
  have e1 : RH1E6S01_0154.sL.t = ((10631345473 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0154.sL]
  rw [e0, e1] at h
  exact h

theorem band_0155 : RS5.BandZeros ((10631345473 : ℝ) / 65536) ((10636493123 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0155.s0 RH1E6S01_0155.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0155.s0 RH1E6S01_0155.rest = RH1E6S01_0155.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0155.s0 :: RH1E6S01_0155.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0155.s0.t = ((10631345473 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0155.s0]
  have e1 : RH1E6S01_0155.sL.t = ((10636493123 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0155.sL]
  rw [e0, e1] at h
  exact h

theorem part_019_1 : RS5.BandZeros ((10626197577 : ℝ) / 65536) ((10636493123 : ℝ) / 65536) 254 := by
  have g0 := band_0154
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0155
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10626197577 : ℝ) / 65536) ((10636493123 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_019_1 <;> assumption
