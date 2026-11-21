-- Prove2me | solution 1 for RH1E6S04.part_025_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:20:31.768242+00:00
-- url     : https://prove2.me/submissions/ec7eb385-0a6b-44fc-aa34-774741aec0ff

import Definitions.Def_RH1E6S04_D025_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0200 : RS5.BandZeros ((20629410476 : ℝ) / 65536) ((20634252370 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0200.s0 RH1E6S04_0200.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0200.s0 RH1E6S04_0200.rest = RH1E6S04_0200.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0200.s0 :: RH1E6S04_0200.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0200.s0.t = ((20629410476 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0200.s0]
  have e1 : RH1E6S04_0200.sL.t = ((20634252370 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0200.sL]
  rw [e0, e1] at h
  exact h

theorem band_0201 : RS5.BandZeros ((20634252370 : ℝ) / 65536) ((20639103672 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0201.s0 RH1E6S04_0201.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0201.s0 RH1E6S04_0201.rest = RH1E6S04_0201.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0201.s0 :: RH1E6S04_0201.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0201.s0.t = ((20634252370 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0201.s0]
  have e1 : RH1E6S04_0201.sL.t = ((20639103672 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0201.sL]
  rw [e0, e1] at h
  exact h

theorem part_025_0 : RS5.BandZeros ((20629410476 : ℝ) / 65536) ((20639103672 : ℝ) / 65536) 254 := by
  have g0 := band_0200
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0201
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20629410476 : ℝ) / 65536) ((20639103672 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_025_0 <;> assumption
