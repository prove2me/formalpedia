-- Prove2me | solution 1 for RH1E6S09.part_072_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T14:35:25.118048+00:00
-- url     : https://prove2.me/submissions/11968aa3-f587-4ff0-9d21-a9537b233d77

import Definitions.Def_RH1E6S09_D072_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0576 : RS5.BandZeros ((38683483045 : ℝ) / 65536) ((38688046063 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0576.s0 RH1E6S09_0576.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0576.s0 RH1E6S09_0576.rest = RH1E6S09_0576.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0576.s0 :: RH1E6S09_0576.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0576.s0.t = ((38683483045 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0576.s0]
  have e1 : RH1E6S09_0576.sL.t = ((38688046063 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0576.sL]
  rw [e0, e1] at h
  exact h

theorem band_0577 : RS5.BandZeros ((38688046063 : ℝ) / 65536) ((38692605654 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0577.s0 RH1E6S09_0577.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0577.s0 RH1E6S09_0577.rest = RH1E6S09_0577.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0577.s0 :: RH1E6S09_0577.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0577.s0.t = ((38688046063 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0577.s0]
  have e1 : RH1E6S09_0577.sL.t = ((38692605654 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0577.sL]
  rw [e0, e1] at h
  exact h

theorem part_072_0 : RS5.BandZeros ((38683483045 : ℝ) / 65536) ((38692605654 : ℝ) / 65536) 254 := by
  have g0 := band_0576
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0577
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38683483045 : ℝ) / 65536) ((38692605654 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_072_0 <;> assumption
