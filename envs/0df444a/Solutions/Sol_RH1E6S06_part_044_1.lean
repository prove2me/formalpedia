-- Prove2me | solution 1 for RH1E6S06.part_044_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T19:07:03.802179+00:00
-- url     : https://prove2.me/submissions/a2302f7c-5546-4aa8-b9c8-dd94bbd933d9

import Definitions.Def_RH1E6S06_D044_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0354 : RS5.BandZeros ((27883335749 : ℝ) / 65536) ((27888032515 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0354.s0 RH1E6S06_0354.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0354.s0 RH1E6S06_0354.rest = RH1E6S06_0354.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0354.s0 :: RH1E6S06_0354.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0354.s0.t = ((27883335749 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0354.s0]
  have e1 : RH1E6S06_0354.sL.t = ((27888032515 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0354.sL]
  rw [e0, e1] at h
  exact h

theorem band_0355 : RS5.BandZeros ((27888032515 : ℝ) / 65536) ((27892726451 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0355.s0 RH1E6S06_0355.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0355.s0 RH1E6S06_0355.rest = RH1E6S06_0355.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0355.s0 :: RH1E6S06_0355.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0355.s0.t = ((27888032515 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0355.s0]
  have e1 : RH1E6S06_0355.sL.t = ((27892726451 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0355.sL]
  rw [e0, e1] at h
  exact h

theorem part_044_1 : RS5.BandZeros ((27883335749 : ℝ) / 65536) ((27892726451 : ℝ) / 65536) 254 := by
  have g0 := band_0354
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0355
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27883335749 : ℝ) / 65536) ((27892726451 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_044_1 <;> assumption
