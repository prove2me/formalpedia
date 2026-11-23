-- Prove2me | solution 1 for RH1E6S13.part_063_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T00:39:22.677399+00:00
-- url     : https://prove2.me/submissions/7537a86f-3f3a-414a-99b5-60926ac9179c

import Definitions.Def_RH1E6S13_D063_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0510 : RS5.BandZeros ((51429073521 : ℝ) / 65536) ((51433503459 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0510.s0 RH1E6S13_0510.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0510.s0 RH1E6S13_0510.rest = RH1E6S13_0510.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0510.s0 :: RH1E6S13_0510.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0510.s0.t = ((51429073521 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0510.s0]
  have e1 : RH1E6S13_0510.sL.t = ((51433503459 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0510.sL]
  rw [e0, e1] at h
  exact h

theorem band_0511 : RS5.BandZeros ((51433503459 : ℝ) / 65536) ((51437977226 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0511.s0 RH1E6S13_0511.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0511.s0 RH1E6S13_0511.rest = RH1E6S13_0511.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0511.s0 :: RH1E6S13_0511.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0511.s0.t = ((51433503459 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0511.s0]
  have e1 : RH1E6S13_0511.sL.t = ((51437977226 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0511.sL]
  rw [e0, e1] at h
  exact h

theorem part_063_3 : RS5.BandZeros ((51429073521 : ℝ) / 65536) ((51437977226 : ℝ) / 65536) 254 := by
  have g0 := band_0510
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0511
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51429073521 : ℝ) / 65536) ((51437977226 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_063_3 <;> assumption
