-- Prove2me | solution 1 for RH1E6S00.part_004_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T20:57:54.351961+00:00
-- url     : https://prove2.me/submissions/a3918ce7-146e-4231-bfd2-018b034e11c2

import Definitions.Def_RH1E6S00_D004_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0036 : RS5.BandZeros ((6747910534 : ℝ) / 65536) ((6753288613 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0036.s0 RH1E6S00_0036.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0036.s0 RH1E6S00_0036.rest = RH1E6S00_0036.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0036.s0 :: RH1E6S00_0036.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0036.s0.t = ((6747910534 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0036.s0]
  have e1 : RH1E6S00_0036.sL.t = ((6753288613 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0036.sL]
  rw [e0, e1] at h
  exact h

theorem band_0037 : RS5.BandZeros ((6753288613 : ℝ) / 65536) ((6758698071 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0037.s0 RH1E6S00_0037.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0037.s0 RH1E6S00_0037.rest = RH1E6S00_0037.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0037.s0 :: RH1E6S00_0037.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0037.s0.t = ((6753288613 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0037.s0]
  have e1 : RH1E6S00_0037.sL.t = ((6758698071 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0037.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_2 : RS5.BandZeros ((6747910534 : ℝ) / 65536) ((6758698071 : ℝ) / 65536) 254 := by
  have g0 := band_0036
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0037
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((6747910534 : ℝ) / 65536) ((6758698071 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_004_2 <;> assumption
