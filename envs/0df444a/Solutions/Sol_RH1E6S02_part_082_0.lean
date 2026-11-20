-- Prove2me | solution 1 for RH1E6S02.part_082_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:02:21.817728+00:00
-- url     : https://prove2.me/submissions/f427ab65-e6d6-4fbe-81e7-e8568500e4d7

import Definitions.Def_RH1E6S02_D082_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0656 : RS5.BandZeros ((16379475136 : ℝ) / 65536) ((16384000000 : ℝ) / 65536) 116 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0656.s0 RH1E6S02_0656.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0656.s0 RH1E6S02_0656.rest = RH1E6S02_0656.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0656.s0 :: RH1E6S02_0656.rest) = 116 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0656.s0.t = ((16379475136 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0656.s0]
  have e1 : RH1E6S02_0656.sL.t = ((16384000000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0656.sL]
  rw [e0, e1] at h
  exact h

theorem part_082_0 : RS5.BandZeros ((16379475136 : ℝ) / 65536) ((16384000000 : ℝ) / 65536) 116 := by
  exact band_0656

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((16379475136 : ℝ) / 65536) ((16384000000 : ℝ) / 65536) 116 := by
  apply RH1E6S02.part_082_0 <;> assumption
