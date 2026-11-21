-- Prove2me | solution 1 for RH1E6S07.part_048_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:13:33.348227+00:00
-- url     : https://prove2.me/submissions/25ba50d9-ca30-4612-a1de-6f52a7396ebc

import Definitions.Def_RH1E6S07_D048_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0386 : RS5.BandZeros ((31292066488 : ℝ) / 65536) ((31296718866 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0386.s0 RH1E6S07_0386.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0386.s0 RH1E6S07_0386.rest = RH1E6S07_0386.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0386.s0 :: RH1E6S07_0386.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0386.s0.t = ((31292066488 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0386.s0]
  have e1 : RH1E6S07_0386.sL.t = ((31296718866 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0386.sL]
  rw [e0, e1] at h
  exact h

theorem band_0387 : RS5.BandZeros ((31296718866 : ℝ) / 65536) ((31301362892 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0387.s0 RH1E6S07_0387.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0387.s0 RH1E6S07_0387.rest = RH1E6S07_0387.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0387.s0 :: RH1E6S07_0387.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0387.s0.t = ((31296718866 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0387.s0]
  have e1 : RH1E6S07_0387.sL.t = ((31301362892 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0387.sL]
  rw [e0, e1] at h
  exact h

theorem part_048_1 : RS5.BandZeros ((31292066488 : ℝ) / 65536) ((31301362892 : ℝ) / 65536) 254 := by
  have g0 := band_0386
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0387
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31292066488 : ℝ) / 65536) ((31301362892 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_048_1 <;> assumption
