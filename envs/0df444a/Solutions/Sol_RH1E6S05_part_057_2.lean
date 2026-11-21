-- Prove2me | solution 1 for RH1E6S05.part_057_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T14:42:14.33173+00:00
-- url     : https://prove2.me/submissions/413ef079-6140-4543-aaa3-86c3ff959d17

import Definitions.Def_RH1E6S05_D057_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0460 : RS5.BandZeros ((25129662523 : ℝ) / 65536) ((25134399034 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0460.s0 RH1E6S05_0460.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0460.s0 RH1E6S05_0460.rest = RH1E6S05_0460.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0460.s0 :: RH1E6S05_0460.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0460.s0.t = ((25129662523 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0460.s0]
  have e1 : RH1E6S05_0460.sL.t = ((25134399034 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0460.sL]
  rw [e0, e1] at h
  exact h

theorem band_0461 : RS5.BandZeros ((25134399034 : ℝ) / 65536) ((25139163491 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0461.s0 RH1E6S05_0461.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0461.s0 RH1E6S05_0461.rest = RH1E6S05_0461.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0461.s0 :: RH1E6S05_0461.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0461.s0.t = ((25134399034 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0461.s0]
  have e1 : RH1E6S05_0461.sL.t = ((25139163491 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0461.sL]
  rw [e0, e1] at h
  exact h

theorem part_057_2 : RS5.BandZeros ((25129662523 : ℝ) / 65536) ((25139163491 : ℝ) / 65536) 254 := by
  have g0 := band_0460
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0461
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25129662523 : ℝ) / 65536) ((25139163491 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_057_2 <;> assumption
