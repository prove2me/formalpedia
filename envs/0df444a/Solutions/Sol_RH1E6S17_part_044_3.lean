-- Prove2me | solution 1 for RH1E6S17.part_044_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:16:26.305715+00:00
-- url     : https://prove2.me/submissions/762b500f-7907-4c32-a5b6-6757a040c295

import Definitions.Def_RH1E6S17_D044_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0358 : RS5.BandZeros ((63827326971 : ℝ) / 65536) ((63831719925 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0358.s0 RH1E6S17_0358.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0358.s0 RH1E6S17_0358.rest = RH1E6S17_0358.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0358.s0 :: RH1E6S17_0358.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0358.s0.t = ((63827326971 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0358.s0]
  have e1 : RH1E6S17_0358.sL.t = ((63831719925 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0358.sL]
  rw [e0, e1] at h
  exact h

theorem band_0359 : RS5.BandZeros ((63831719925 : ℝ) / 65536) ((63836095626 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0359.s0 RH1E6S17_0359.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0359.s0 RH1E6S17_0359.rest = RH1E6S17_0359.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0359.s0 :: RH1E6S17_0359.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0359.s0.t = ((63831719925 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0359.s0]
  have e1 : RH1E6S17_0359.sL.t = ((63836095626 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0359.sL]
  rw [e0, e1] at h
  exact h

theorem part_044_3 : RS5.BandZeros ((63827326971 : ℝ) / 65536) ((63836095626 : ℝ) / 65536) 254 := by
  have g0 := band_0358
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0359
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63827326971 : ℝ) / 65536) ((63836095626 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_044_3 <;> assumption
