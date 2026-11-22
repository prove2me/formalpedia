-- Prove2me | solution 1 for RH1E6S12.part_091_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:45:38.67318+00:00
-- url     : https://prove2.me/submissions/b056a601-05da-4530-a66f-fc464b5d1123

import Definitions.Def_RH1E6S12_D091_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0730 : RS5.BandZeros ((49150449726 : ℝ) / 65536) ((49152000000 : ℝ) / 65536) 44 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0730.s0 RH1E6S12_0730.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0730.s0 RH1E6S12_0730.rest = RH1E6S12_0730.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0730.s0 :: RH1E6S12_0730.rest) = 44 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0730.s0.t = ((49150449726 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0730.s0]
  have e1 : RH1E6S12_0730.sL.t = ((49152000000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0730.sL]
  rw [e0, e1] at h
  exact h

theorem part_091_1 : RS5.BandZeros ((49150449726 : ℝ) / 65536) ((49152000000 : ℝ) / 65536) 44 := by
  exact band_0730

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((49150449726 : ℝ) / 65536) ((49152000000 : ℝ) / 65536) 44 := by
  apply RH1E6S12.part_091_1 <;> assumption
