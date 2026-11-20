-- Prove2me | solution 1 for RH1E6S00.part_004_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T20:57:52.347838+00:00
-- url     : https://prove2.me/submissions/4d96ae1c-3744-4873-bab1-9f2dccf5a292

import Definitions.Def_RH1E6S00_D004_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0034 : RS5.BandZeros ((6737121220 : ℝ) / 65536) ((6742510795 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0034.s0 RH1E6S00_0034.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0034.s0 RH1E6S00_0034.rest = RH1E6S00_0034.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0034.s0 :: RH1E6S00_0034.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0034.s0.t = ((6737121220 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0034.s0]
  have e1 : RH1E6S00_0034.sL.t = ((6742510795 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0034.sL]
  rw [e0, e1] at h
  exact h

theorem band_0035 : RS5.BandZeros ((6742510795 : ℝ) / 65536) ((6747910534 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0035.s0 RH1E6S00_0035.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0035.s0 RH1E6S00_0035.rest = RH1E6S00_0035.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0035.s0 :: RH1E6S00_0035.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0035.s0.t = ((6742510795 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0035.s0]
  have e1 : RH1E6S00_0035.sL.t = ((6747910534 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0035.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_1 : RS5.BandZeros ((6737121220 : ℝ) / 65536) ((6747910534 : ℝ) / 65536) 254 := by
  have g0 := band_0034
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0035
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((6737121220 : ℝ) / 65536) ((6747910534 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_004_1 <;> assumption
