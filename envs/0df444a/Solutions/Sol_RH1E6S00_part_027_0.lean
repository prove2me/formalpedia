-- Prove2me | solution 1 for RH1E6S00.part_027_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:42:26.968191+00:00
-- url     : https://prove2.me/submissions/8305e39b-2e77-464f-ad16-a3cd3ddf8c16

import Definitions.Def_RH1E6S00_D027_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0216 : RS5.BandZeros ((7711155025 : ℝ) / 65536) ((7716470654 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0216.s0 RH1E6S00_0216.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0216.s0 RH1E6S00_0216.rest = RH1E6S00_0216.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0216.s0 :: RH1E6S00_0216.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0216.s0.t = ((7711155025 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0216.s0]
  have e1 : RH1E6S00_0216.sL.t = ((7716470654 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0216.sL]
  rw [e0, e1] at h
  exact h

theorem band_0217 : RS5.BandZeros ((7716470654 : ℝ) / 65536) ((7721775448 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0217.s0 RH1E6S00_0217.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0217.s0 RH1E6S00_0217.rest = RH1E6S00_0217.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0217.s0 :: RH1E6S00_0217.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0217.s0.t = ((7716470654 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0217.s0]
  have e1 : RH1E6S00_0217.sL.t = ((7721775448 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0217.sL]
  rw [e0, e1] at h
  exact h

theorem part_027_0 : RS5.BandZeros ((7711155025 : ℝ) / 65536) ((7721775448 : ℝ) / 65536) 254 := by
  have g0 := band_0216
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0217
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7711155025 : ℝ) / 65536) ((7721775448 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_027_0 <;> assumption
