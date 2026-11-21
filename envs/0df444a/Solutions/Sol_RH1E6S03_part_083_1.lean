-- Prove2me | solution 1 for RH1E6S03.part_083_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T08:21:08.468092+00:00
-- url     : https://prove2.me/submissions/e4d20ab6-8b19-4beb-bf31-c41d7a36729a

import Definitions.Def_RH1E6S03_D083_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0666 : RS5.BandZeros ((19643655566 : ℝ) / 65536) ((19648500353 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0666.s0 RH1E6S03_0666.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0666.s0 RH1E6S03_0666.rest = RH1E6S03_0666.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0666.s0 :: RH1E6S03_0666.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0666.s0.t = ((19643655566 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0666.s0]
  have e1 : RH1E6S03_0666.sL.t = ((19648500353 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0666.sL]
  rw [e0, e1] at h
  exact h

theorem band_0667 : RS5.BandZeros ((19648500353 : ℝ) / 65536) ((19653345029 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0667.s0 RH1E6S03_0667.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0667.s0 RH1E6S03_0667.rest = RH1E6S03_0667.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0667.s0 :: RH1E6S03_0667.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0667.s0.t = ((19648500353 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0667.s0]
  have e1 : RH1E6S03_0667.sL.t = ((19653345029 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0667.sL]
  rw [e0, e1] at h
  exact h

theorem part_083_1 : RS5.BandZeros ((19643655566 : ℝ) / 65536) ((19653345029 : ℝ) / 65536) 254 := by
  have g0 := band_0666
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0667
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((19643655566 : ℝ) / 65536) ((19653345029 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_083_1 <;> assumption
