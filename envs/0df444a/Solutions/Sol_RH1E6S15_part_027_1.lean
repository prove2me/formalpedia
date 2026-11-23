-- Prove2me | solution 1 for RH1E6S15.part_027_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T09:27:11.614794+00:00
-- url     : https://prove2.me/submissions/c9fe7642-998c-465f-9ba4-e6077112ce22

import Definitions.Def_RH1E6S15_D027_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0218 : RS5.BandZeros ((56669771994 : ℝ) / 65536) ((56674191540 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0218.s0 RH1E6S15_0218.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0218.s0 RH1E6S15_0218.rest = RH1E6S15_0218.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0218.s0 :: RH1E6S15_0218.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0218.s0.t = ((56669771994 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0218.s0]
  have e1 : RH1E6S15_0218.sL.t = ((56674191540 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0218.sL]
  rw [e0, e1] at h
  exact h

theorem band_0219 : RS5.BandZeros ((56674191540 : ℝ) / 65536) ((56678611386 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0219.s0 RH1E6S15_0219.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0219.s0 RH1E6S15_0219.rest = RH1E6S15_0219.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0219.s0 :: RH1E6S15_0219.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0219.s0.t = ((56674191540 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0219.s0]
  have e1 : RH1E6S15_0219.sL.t = ((56678611386 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0219.sL]
  rw [e0, e1] at h
  exact h

theorem part_027_1 : RS5.BandZeros ((56669771994 : ℝ) / 65536) ((56678611386 : ℝ) / 65536) 254 := by
  have g0 := band_0218
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0219
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56669771994 : ℝ) / 65536) ((56678611386 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_027_1 <;> assumption
