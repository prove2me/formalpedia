-- Prove2me | solution 1 for RH1E6S09.part_007_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T08:30:56.567147+00:00
-- url     : https://prove2.me/submissions/516f994b-12d3-4a76-bd22-9c91d49ab95f

import Definitions.Def_RH1E6S09_D007_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0060 : RS5.BandZeros ((36320403727 : ℝ) / 65536) ((36324986713 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0060.s0 RH1E6S09_0060.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0060.s0 RH1E6S09_0060.rest = RH1E6S09_0060.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0060.s0 :: RH1E6S09_0060.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0060.s0.t = ((36320403727 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0060.s0]
  have e1 : RH1E6S09_0060.sL.t = ((36324986713 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0060.sL]
  rw [e0, e1] at h
  exact h

theorem band_0061 : RS5.BandZeros ((36324986713 : ℝ) / 65536) ((36329598864 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0061.s0 RH1E6S09_0061.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0061.s0 RH1E6S09_0061.rest = RH1E6S09_0061.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0061.s0 :: RH1E6S09_0061.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0061.s0.t = ((36324986713 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0061.s0]
  have e1 : RH1E6S09_0061.sL.t = ((36329598864 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0061.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_2 : RS5.BandZeros ((36320403727 : ℝ) / 65536) ((36329598864 : ℝ) / 65536) 254 := by
  have g0 := band_0060
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0061
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36320403727 : ℝ) / 65536) ((36329598864 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_007_2 <;> assumption
