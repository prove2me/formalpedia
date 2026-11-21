-- Prove2me | solution 1 for RH1E6S06.part_081_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:32:08.62401+00:00
-- url     : https://prove2.me/submissions/ed8419af-d895-48b2-8c98-1f93cd450a6c

import Definitions.Def_RH1E6S06_D081_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0648 : RS5.BandZeros ((29262570968 : ℝ) / 65536) ((29267247620 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0648.s0 RH1E6S06_0648.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0648.s0 RH1E6S06_0648.rest = RH1E6S06_0648.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0648.s0 :: RH1E6S06_0648.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0648.s0.t = ((29262570968 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0648.s0]
  have e1 : RH1E6S06_0648.sL.t = ((29267247620 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0648.sL]
  rw [e0, e1] at h
  exact h

theorem band_0649 : RS5.BandZeros ((29267247620 : ℝ) / 65536) ((29271922242 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0649.s0 RH1E6S06_0649.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0649.s0 RH1E6S06_0649.rest = RH1E6S06_0649.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0649.s0 :: RH1E6S06_0649.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0649.s0.t = ((29267247620 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0649.s0]
  have e1 : RH1E6S06_0649.sL.t = ((29271922242 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0649.sL]
  rw [e0, e1] at h
  exact h

theorem part_081_0 : RS5.BandZeros ((29262570968 : ℝ) / 65536) ((29271922242 : ℝ) / 65536) 254 := by
  have g0 := band_0648
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0649
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((29262570968 : ℝ) / 65536) ((29271922242 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_081_0 <;> assumption
