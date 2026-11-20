-- Prove2me | solution 1 for RH1E6S00.part_000_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T20:53:03.382563+00:00
-- url     : https://prove2.me/submissions/3520f0b0-a8b9-4799-905f-5e2e9742b07e

import Definitions.Def_RH1E6S00_D000_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0002 : RS5.BandZeros ((6564428235 : ℝ) / 65536) ((6569842903 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0002.s0 RH1E6S00_0002.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0002.s0 RH1E6S00_0002.rest = RH1E6S00_0002.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0002.s0 :: RH1E6S00_0002.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0002.s0.t = ((6564428235 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0002.s0]
  have e1 : RH1E6S00_0002.sL.t = ((6569842903 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0002.sL]
  rw [e0, e1] at h
  exact h

theorem band_0003 : RS5.BandZeros ((6569842903 : ℝ) / 65536) ((6575235837 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0003.s0 RH1E6S00_0003.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0003.s0 RH1E6S00_0003.rest = RH1E6S00_0003.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0003.s0 :: RH1E6S00_0003.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0003.s0.t = ((6569842903 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0003.s0]
  have e1 : RH1E6S00_0003.sL.t = ((6575235837 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0003.sL]
  rw [e0, e1] at h
  exact h

theorem part_000_1 : RS5.BandZeros ((6564428235 : ℝ) / 65536) ((6575235837 : ℝ) / 65536) 254 := by
  have g0 := band_0002
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0003
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((6564428235 : ℝ) / 65536) ((6575235837 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_000_1 <;> assumption
