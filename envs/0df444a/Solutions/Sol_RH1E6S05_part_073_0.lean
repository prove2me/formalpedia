-- Prove2me | solution 1 for RH1E6S05.part_073_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T16:10:27.062104+00:00
-- url     : https://prove2.me/submissions/ab3fea11-afee-4b09-b88c-aef7acf5c1f1

import Definitions.Def_RH1E6S05_D073_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0584 : RS5.BandZeros ((25717524893 : ℝ) / 65536) ((25722251487 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0584.s0 RH1E6S05_0584.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0584.s0 RH1E6S05_0584.rest = RH1E6S05_0584.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0584.s0 :: RH1E6S05_0584.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0584.s0.t = ((25717524893 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0584.s0]
  have e1 : RH1E6S05_0584.sL.t = ((25722251487 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0584.sL]
  rw [e0, e1] at h
  exact h

theorem band_0585 : RS5.BandZeros ((25722251487 : ℝ) / 65536) ((25726996647 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0585.s0 RH1E6S05_0585.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0585.s0 RH1E6S05_0585.rest = RH1E6S05_0585.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0585.s0 :: RH1E6S05_0585.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0585.s0.t = ((25722251487 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0585.s0]
  have e1 : RH1E6S05_0585.sL.t = ((25726996647 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0585.sL]
  rw [e0, e1] at h
  exact h

theorem part_073_0 : RS5.BandZeros ((25717524893 : ℝ) / 65536) ((25726996647 : ℝ) / 65536) 254 := by
  have g0 := band_0584
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0585
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25717524893 : ℝ) / 65536) ((25726996647 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_073_0 <;> assumption
