-- Prove2me | solution 1 for RH1E6S12.part_054_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T10:02:37.869803+00:00
-- url     : https://prove2.me/submissions/5a83c6ee-0468-4f18-b8e4-850874d2a2a7

import Definitions.Def_RH1E6S12_D054_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0432 : RS5.BandZeros ((47815787414 : ℝ) / 65536) ((47820258755 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0432.s0 RH1E6S12_0432.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0432.s0 RH1E6S12_0432.rest = RH1E6S12_0432.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0432.s0 :: RH1E6S12_0432.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0432.s0.t = ((47815787414 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0432.s0]
  have e1 : RH1E6S12_0432.sL.t = ((47820258755 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0432.sL]
  rw [e0, e1] at h
  exact h

theorem band_0433 : RS5.BandZeros ((47820258755 : ℝ) / 65536) ((47824742808 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0433.s0 RH1E6S12_0433.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0433.s0 RH1E6S12_0433.rest = RH1E6S12_0433.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0433.s0 :: RH1E6S12_0433.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0433.s0.t = ((47820258755 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0433.s0]
  have e1 : RH1E6S12_0433.sL.t = ((47824742808 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0433.sL]
  rw [e0, e1] at h
  exact h

theorem part_054_0 : RS5.BandZeros ((47815787414 : ℝ) / 65536) ((47824742808 : ℝ) / 65536) 254 := by
  have g0 := band_0432
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0433
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47815787414 : ℝ) / 65536) ((47824742808 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_054_0 <;> assumption
