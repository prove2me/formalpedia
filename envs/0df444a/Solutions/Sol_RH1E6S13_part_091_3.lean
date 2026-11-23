-- Prove2me | solution 1 for RH1E6S13.part_091_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:22:26.449053+00:00
-- url     : https://prove2.me/submissions/67380c83-3a8b-46d0-b9a9-3e88649cc23c

import Definitions.Def_RH1E6S13_D091_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0734 : RS5.BandZeros ((52426450709 : ℝ) / 65536) ((52428800000 : ℝ) / 65536) 67 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0734.s0 RH1E6S13_0734.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0734.s0 RH1E6S13_0734.rest = RH1E6S13_0734.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0734.s0 :: RH1E6S13_0734.rest) = 67 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0734.s0.t = ((52426450709 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0734.s0]
  have e1 : RH1E6S13_0734.sL.t = ((52428800000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0734.sL]
  rw [e0, e1] at h
  exact h

theorem part_091_3 : RS5.BandZeros ((52426450709 : ℝ) / 65536) ((52428800000 : ℝ) / 65536) 67 := by
  exact band_0734

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((52426450709 : ℝ) / 65536) ((52428800000 : ℝ) / 65536) 67 := by
  apply RH1E6S13.part_091_3 <;> assumption
