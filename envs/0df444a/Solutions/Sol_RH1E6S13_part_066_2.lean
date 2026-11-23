-- Prove2me | solution 1 for RH1E6S13.part_066_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T00:47:45.945805+00:00
-- url     : https://prove2.me/submissions/c86756f4-7d36-427f-b36f-07889f3dc66f

import Definitions.Def_RH1E6S13_D066_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0532 : RS5.BandZeros ((51527085994 : ℝ) / 65536) ((51531541526 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0532.s0 RH1E6S13_0532.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0532.s0 RH1E6S13_0532.rest = RH1E6S13_0532.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0532.s0 :: RH1E6S13_0532.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0532.s0.t = ((51527085994 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0532.s0]
  have e1 : RH1E6S13_0532.sL.t = ((51531541526 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0532.sL]
  rw [e0, e1] at h
  exact h

theorem band_0533 : RS5.BandZeros ((51531541526 : ℝ) / 65536) ((51536005796 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0533.s0 RH1E6S13_0533.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0533.s0 RH1E6S13_0533.rest = RH1E6S13_0533.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0533.s0 :: RH1E6S13_0533.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0533.s0.t = ((51531541526 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0533.s0]
  have e1 : RH1E6S13_0533.sL.t = ((51536005796 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0533.sL]
  rw [e0, e1] at h
  exact h

theorem part_066_2 : RS5.BandZeros ((51527085994 : ℝ) / 65536) ((51536005796 : ℝ) / 65536) 254 := by
  have g0 := band_0532
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0533
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51527085994 : ℝ) / 65536) ((51536005796 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_066_2 <;> assumption
