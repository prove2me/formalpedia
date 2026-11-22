-- Prove2me | solution 1 for RH1E6S09.part_043_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:09:54.009715+00:00
-- url     : https://prove2.me/submissions/eaae9984-a4ef-4162-a0af-bb6473acb2ef

import Definitions.Def_RH1E6S09_D043_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0344 : RS5.BandZeros ((37622611173 : ℝ) / 65536) ((37627211423 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0344.s0 RH1E6S09_0344.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0344.s0 RH1E6S09_0344.rest = RH1E6S09_0344.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0344.s0 :: RH1E6S09_0344.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0344.s0.t = ((37622611173 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0344.s0]
  have e1 : RH1E6S09_0344.sL.t = ((37627211423 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0344.sL]
  rw [e0, e1] at h
  exact h

theorem band_0345 : RS5.BandZeros ((37627211423 : ℝ) / 65536) ((37631797477 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0345.s0 RH1E6S09_0345.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0345.s0 RH1E6S09_0345.rest = RH1E6S09_0345.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0345.s0 :: RH1E6S09_0345.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0345.s0.t = ((37627211423 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0345.s0]
  have e1 : RH1E6S09_0345.sL.t = ((37631797477 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0345.sL]
  rw [e0, e1] at h
  exact h

theorem part_043_0 : RS5.BandZeros ((37622611173 : ℝ) / 65536) ((37631797477 : ℝ) / 65536) 254 := by
  have g0 := band_0344
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0345
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37622611173 : ℝ) / 65536) ((37631797477 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_043_0 <;> assumption
