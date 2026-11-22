-- Prove2me | solution 1 for RH1E6S09.part_039_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:59:05.645146+00:00
-- url     : https://prove2.me/submissions/9f052bcb-0bde-4e61-9aca-258313778c6a

import Definitions.Def_RH1E6S09_D039_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0316 : RS5.BandZeros ((37494405773 : ℝ) / 65536) ((37498995141 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0316.s0 RH1E6S09_0316.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0316.s0 RH1E6S09_0316.rest = RH1E6S09_0316.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0316.s0 :: RH1E6S09_0316.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0316.s0.t = ((37494405773 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0316.s0]
  have e1 : RH1E6S09_0316.sL.t = ((37498995141 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0316.sL]
  rw [e0, e1] at h
  exact h

theorem band_0317 : RS5.BandZeros ((37498995141 : ℝ) / 65536) ((37503598443 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0317.s0 RH1E6S09_0317.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0317.s0 RH1E6S09_0317.rest = RH1E6S09_0317.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0317.s0 :: RH1E6S09_0317.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0317.s0.t = ((37498995141 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0317.s0]
  have e1 : RH1E6S09_0317.sL.t = ((37503598443 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0317.sL]
  rw [e0, e1] at h
  exact h

theorem part_039_2 : RS5.BandZeros ((37494405773 : ℝ) / 65536) ((37503598443 : ℝ) / 65536) 254 := by
  have g0 := band_0316
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0317
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37494405773 : ℝ) / 65536) ((37503598443 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_039_2 <;> assumption
