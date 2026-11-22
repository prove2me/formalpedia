-- Prove2me | solution 1 for RH1E6S09.part_057_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:50:33.741671+00:00
-- url     : https://prove2.me/submissions/22f6f4e2-3cc6-4269-9330-2a6ad8d594ff

import Definitions.Def_RH1E6S09_D057_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0462 : RS5.BandZeros ((38162518118 : ℝ) / 65536) ((38167093062 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0462.s0 RH1E6S09_0462.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0462.s0 RH1E6S09_0462.rest = RH1E6S09_0462.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0462.s0 :: RH1E6S09_0462.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0462.s0.t = ((38162518118 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0462.s0]
  have e1 : RH1E6S09_0462.sL.t = ((38167093062 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0462.sL]
  rw [e0, e1] at h
  exact h

theorem band_0463 : RS5.BandZeros ((38167093062 : ℝ) / 65536) ((38171655643 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0463.s0 RH1E6S09_0463.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0463.s0 RH1E6S09_0463.rest = RH1E6S09_0463.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0463.s0 :: RH1E6S09_0463.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0463.s0.t = ((38167093062 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0463.s0]
  have e1 : RH1E6S09_0463.sL.t = ((38171655643 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0463.sL]
  rw [e0, e1] at h
  exact h

theorem part_057_3 : RS5.BandZeros ((38162518118 : ℝ) / 65536) ((38171655643 : ℝ) / 65536) 254 := by
  have g0 := band_0462
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0463
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38162518118 : ℝ) / 65536) ((38171655643 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_057_3 <;> assumption
