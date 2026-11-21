-- Prove2me | solution 1 for RH1E6S04.part_054_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:27:48.966501+00:00
-- url     : https://prove2.me/submissions/784827f3-97c2-4f51-aab6-78e255811d1c

import Definitions.Def_RH1E6S04_D054_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0436 : RS5.BandZeros ((21767037274 : ℝ) / 65536) ((21771845807 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0436.s0 RH1E6S04_0436.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0436.s0 RH1E6S04_0436.rest = RH1E6S04_0436.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0436.s0 :: RH1E6S04_0436.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0436.s0.t = ((21767037274 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0436.s0]
  have e1 : RH1E6S04_0436.sL.t = ((21771845807 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0436.sL]
  rw [e0, e1] at h
  exact h

theorem band_0437 : RS5.BandZeros ((21771845807 : ℝ) / 65536) ((21776654243 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0437.s0 RH1E6S04_0437.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0437.s0 RH1E6S04_0437.rest = RH1E6S04_0437.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0437.s0 :: RH1E6S04_0437.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0437.s0.t = ((21771845807 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0437.s0]
  have e1 : RH1E6S04_0437.sL.t = ((21776654243 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0437.sL]
  rw [e0, e1] at h
  exact h

theorem part_054_2 : RS5.BandZeros ((21767037274 : ℝ) / 65536) ((21776654243 : ℝ) / 65536) 254 := by
  have g0 := band_0436
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0437
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((21767037274 : ℝ) / 65536) ((21776654243 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_054_2 <;> assumption
