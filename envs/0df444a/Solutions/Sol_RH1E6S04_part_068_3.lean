-- Prove2me | solution 1 for RH1E6S04.part_068_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T11:00:29.632204+00:00
-- url     : https://prove2.me/submissions/7b64a919-6cd5-42ce-b32d-0717a98384bf

import Definitions.Def_RH1E6S04_D068_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0550 : RS5.BandZeros ((22314597102 : ℝ) / 65536) ((22319385233 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0550.s0 RH1E6S04_0550.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0550.s0 RH1E6S04_0550.rest = RH1E6S04_0550.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0550.s0 :: RH1E6S04_0550.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0550.s0.t = ((22314597102 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0550.s0]
  have e1 : RH1E6S04_0550.sL.t = ((22319385233 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0550.sL]
  rw [e0, e1] at h
  exact h

theorem band_0551 : RS5.BandZeros ((22319385233 : ℝ) / 65536) ((22324173270 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0551.s0 RH1E6S04_0551.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0551.s0 RH1E6S04_0551.rest = RH1E6S04_0551.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0551.s0 :: RH1E6S04_0551.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0551.s0.t = ((22319385233 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0551.s0]
  have e1 : RH1E6S04_0551.sL.t = ((22324173270 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0551.sL]
  rw [e0, e1] at h
  exact h

theorem part_068_3 : RS5.BandZeros ((22314597102 : ℝ) / 65536) ((22324173270 : ℝ) / 65536) 254 := by
  have g0 := band_0550
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0551
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22314597102 : ℝ) / 65536) ((22324173270 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_068_3 <;> assumption
