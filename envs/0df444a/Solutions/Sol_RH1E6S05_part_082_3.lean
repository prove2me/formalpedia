-- Prove2me | solution 1 for RH1E6S05.part_082_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:04:56.049352+00:00
-- url     : https://prove2.me/submissions/45170baa-8948-44e3-a723-79d6dd699800

import Definitions.Def_RH1E6S05_D082_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0662 : RS5.BandZeros ((26086709264 : ℝ) / 65536) ((26091420455 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0662.s0 RH1E6S05_0662.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0662.s0 RH1E6S05_0662.rest = RH1E6S05_0662.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0662.s0 :: RH1E6S05_0662.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0662.s0.t = ((26086709264 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0662.s0]
  have e1 : RH1E6S05_0662.sL.t = ((26091420455 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0662.sL]
  rw [e0, e1] at h
  exact h

theorem band_0663 : RS5.BandZeros ((26091420455 : ℝ) / 65536) ((26096159500 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0663.s0 RH1E6S05_0663.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0663.s0 RH1E6S05_0663.rest = RH1E6S05_0663.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0663.s0 :: RH1E6S05_0663.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0663.s0.t = ((26091420455 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0663.s0]
  have e1 : RH1E6S05_0663.sL.t = ((26096159500 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0663.sL]
  rw [e0, e1] at h
  exact h

theorem part_082_3 : RS5.BandZeros ((26086709264 : ℝ) / 65536) ((26096159500 : ℝ) / 65536) 254 := by
  have g0 := band_0662
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0663
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((26086709264 : ℝ) / 65536) ((26096159500 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_082_3 <;> assumption
