-- Prove2me | solution 1 for RH1E6S07.part_021_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T23:54:49.732695+00:00
-- url     : https://prove2.me/submissions/b801c955-4c5f-420c-8feb-b8b535912405

import Definitions.Def_RH1E6S07_D021_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0172 : RS5.BandZeros ((30294834606 : ℝ) / 65536) ((30299492240 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0172.s0 RH1E6S07_0172.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0172.s0 RH1E6S07_0172.rest = RH1E6S07_0172.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0172.s0 :: RH1E6S07_0172.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0172.s0.t = ((30294834606 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0172.s0]
  have e1 : RH1E6S07_0172.sL.t = ((30299492240 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0172.sL]
  rw [e0, e1] at h
  exact h

theorem band_0173 : RS5.BandZeros ((30299492240 : ℝ) / 65536) ((30304170831 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0173.s0 RH1E6S07_0173.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0173.s0 RH1E6S07_0173.rest = RH1E6S07_0173.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0173.s0 :: RH1E6S07_0173.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0173.s0.t = ((30299492240 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0173.s0]
  have e1 : RH1E6S07_0173.sL.t = ((30304170831 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0173.sL]
  rw [e0, e1] at h
  exact h

theorem part_021_2 : RS5.BandZeros ((30294834606 : ℝ) / 65536) ((30304170831 : ℝ) / 65536) 254 := by
  have g0 := band_0172
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0173
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30294834606 : ℝ) / 65536) ((30304170831 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_021_2 <;> assumption
