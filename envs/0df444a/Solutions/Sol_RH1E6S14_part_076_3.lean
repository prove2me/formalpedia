-- Prove2me | solution 1 for RH1E6S14.part_076_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T06:50:10.414692+00:00
-- url     : https://prove2.me/submissions/f009c7f1-9c2f-4968-ac30-4ea955e5bc1a

import Definitions.Def_RH1E6S14_D076_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0614 : RS5.BandZeros ((55154535177 : ℝ) / 65536) ((55158953340 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0614.s0 RH1E6S14_0614.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0614.s0 RH1E6S14_0614.rest = RH1E6S14_0614.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0614.s0 :: RH1E6S14_0614.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0614.s0.t = ((55154535177 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0614.s0]
  have e1 : RH1E6S14_0614.sL.t = ((55158953340 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0614.sL]
  rw [e0, e1] at h
  exact h

theorem band_0615 : RS5.BandZeros ((55158953340 : ℝ) / 65536) ((55163403324 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0615.s0 RH1E6S14_0615.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0615.s0 RH1E6S14_0615.rest = RH1E6S14_0615.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0615.s0 :: RH1E6S14_0615.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0615.s0.t = ((55158953340 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0615.s0]
  have e1 : RH1E6S14_0615.sL.t = ((55163403324 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0615.sL]
  rw [e0, e1] at h
  exact h

theorem part_076_3 : RS5.BandZeros ((55154535177 : ℝ) / 65536) ((55163403324 : ℝ) / 65536) 254 := by
  have g0 := band_0614
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0615
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55154535177 : ℝ) / 65536) ((55163403324 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_076_3 <;> assumption
