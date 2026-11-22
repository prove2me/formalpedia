-- Prove2me | solution 1 for RH1E6S09.part_077_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T15:07:40.091309+00:00
-- url     : https://prove2.me/submissions/24867659-896d-4f16-95af-dfe9848407ae

import Definitions.Def_RH1E6S09_D077_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0616 : RS5.BandZeros ((38866121402 : ℝ) / 65536) ((38870677840 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0616.s0 RH1E6S09_0616.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0616.s0 RH1E6S09_0616.rest = RH1E6S09_0616.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0616.s0 :: RH1E6S09_0616.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0616.s0.t = ((38866121402 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0616.s0]
  have e1 : RH1E6S09_0616.sL.t = ((38870677840 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0616.sL]
  rw [e0, e1] at h
  exact h

theorem band_0617 : RS5.BandZeros ((38870677840 : ℝ) / 65536) ((38875254345 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0617.s0 RH1E6S09_0617.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0617.s0 RH1E6S09_0617.rest = RH1E6S09_0617.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0617.s0 :: RH1E6S09_0617.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0617.s0.t = ((38870677840 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0617.s0]
  have e1 : RH1E6S09_0617.sL.t = ((38875254345 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0617.sL]
  rw [e0, e1] at h
  exact h

theorem part_077_0 : RS5.BandZeros ((38866121402 : ℝ) / 65536) ((38875254345 : ℝ) / 65536) 254 := by
  have g0 := band_0616
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0617
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38866121402 : ℝ) / 65536) ((38875254345 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_077_0 <;> assumption
