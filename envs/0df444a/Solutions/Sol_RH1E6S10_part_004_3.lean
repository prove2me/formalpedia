-- Prove2me | solution 1 for RH1E6S10.part_004_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T17:20:45.813504+00:00
-- url     : https://prove2.me/submissions/45bb92cf-9085-4a06-9c34-e40f07411f41

import Definitions.Def_RH1E6S10_D004_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0038 : RS5.BandZeros ((39494908597 : ℝ) / 65536) ((39499458441 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0038.s0 RH1E6S10_0038.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0038.s0 RH1E6S10_0038.rest = RH1E6S10_0038.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0038.s0 :: RH1E6S10_0038.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0038.s0.t = ((39494908597 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0038.s0]
  have e1 : RH1E6S10_0038.sL.t = ((39499458441 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0038.sL]
  rw [e0, e1] at h
  exact h

theorem band_0039 : RS5.BandZeros ((39499458441 : ℝ) / 65536) ((39503999265 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0039.s0 RH1E6S10_0039.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0039.s0 RH1E6S10_0039.rest = RH1E6S10_0039.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0039.s0 :: RH1E6S10_0039.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0039.s0.t = ((39499458441 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0039.s0]
  have e1 : RH1E6S10_0039.sL.t = ((39503999265 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0039.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_3 : RS5.BandZeros ((39494908597 : ℝ) / 65536) ((39503999265 : ℝ) / 65536) 254 := by
  have g0 := band_0038
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0039
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39494908597 : ℝ) / 65536) ((39503999265 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_004_3 <;> assumption
