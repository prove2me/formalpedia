-- Prove2me | solution 1 for RH1E6S13.part_061_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T00:25:16.954337+00:00
-- url     : https://prove2.me/submissions/a6a10734-d465-4c27-a85f-43349a3bfc4d

import Definitions.Def_RH1E6S13_D061_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0488 : RS5.BandZeros ((51331018807 : ℝ) / 65536) ((51335467013 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0488.s0 RH1E6S13_0488.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0488.s0 RH1E6S13_0488.rest = RH1E6S13_0488.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0488.s0 :: RH1E6S13_0488.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0488.s0.t = ((51331018807 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0488.s0]
  have e1 : RH1E6S13_0488.sL.t = ((51335467013 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0488.sL]
  rw [e0, e1] at h
  exact h

theorem band_0489 : RS5.BandZeros ((51335467013 : ℝ) / 65536) ((51339941507 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0489.s0 RH1E6S13_0489.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0489.s0 RH1E6S13_0489.rest = RH1E6S13_0489.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0489.s0 :: RH1E6S13_0489.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0489.s0.t = ((51335467013 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0489.s0]
  have e1 : RH1E6S13_0489.sL.t = ((51339941507 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0489.sL]
  rw [e0, e1] at h
  exact h

theorem part_061_0 : RS5.BandZeros ((51331018807 : ℝ) / 65536) ((51339941507 : ℝ) / 65536) 254 := by
  have g0 := band_0488
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0489
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51331018807 : ℝ) / 65536) ((51339941507 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_061_0 <;> assumption
