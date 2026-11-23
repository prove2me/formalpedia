-- Prove2me | solution 1 for RH1E6S14.part_089_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:34:25.125214+00:00
-- url     : https://prove2.me/submissions/d396b52d-4640-4562-bae9-ba07d1b1f5cd

import Definitions.Def_RH1E6S14_D089_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0712 : RS5.BandZeros ((55588518710 : ℝ) / 65536) ((55592956469 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0712.s0 RH1E6S14_0712.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0712.s0 RH1E6S14_0712.rest = RH1E6S14_0712.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0712.s0 :: RH1E6S14_0712.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0712.s0.t = ((55588518710 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0712.s0]
  have e1 : RH1E6S14_0712.sL.t = ((55592956469 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0712.sL]
  rw [e0, e1] at h
  exact h

theorem band_0713 : RS5.BandZeros ((55592956469 : ℝ) / 65536) ((55597375840 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0713.s0 RH1E6S14_0713.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0713.s0 RH1E6S14_0713.rest = RH1E6S14_0713.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0713.s0 :: RH1E6S14_0713.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0713.s0.t = ((55592956469 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0713.s0]
  have e1 : RH1E6S14_0713.sL.t = ((55597375840 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0713.sL]
  rw [e0, e1] at h
  exact h

theorem part_089_0 : RS5.BandZeros ((55588518710 : ℝ) / 65536) ((55597375840 : ℝ) / 65536) 254 := by
  have g0 := band_0712
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0713
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55588518710 : ℝ) / 65536) ((55597375840 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_089_0 <;> assumption
