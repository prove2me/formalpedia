-- Prove2me | solution 1 for RH1E6S14.part_085_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:22:46.936476+00:00
-- url     : https://prove2.me/submissions/8de9130e-4106-425e-bba1-0e9b07cd5815

import Definitions.Def_RH1E6S14_D085_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0682 : RS5.BandZeros ((55455704027 : ℝ) / 65536) ((55460129777 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0682.s0 RH1E6S14_0682.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0682.s0 RH1E6S14_0682.rest = RH1E6S14_0682.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0682.s0 :: RH1E6S14_0682.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0682.s0.t = ((55455704027 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0682.s0]
  have e1 : RH1E6S14_0682.sL.t = ((55460129777 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0682.sL]
  rw [e0, e1] at h
  exact h

theorem band_0683 : RS5.BandZeros ((55460129777 : ℝ) / 65536) ((55464564624 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0683.s0 RH1E6S14_0683.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0683.s0 RH1E6S14_0683.rest = RH1E6S14_0683.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0683.s0 :: RH1E6S14_0683.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0683.s0.t = ((55460129777 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0683.s0]
  have e1 : RH1E6S14_0683.sL.t = ((55464564624 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0683.sL]
  rw [e0, e1] at h
  exact h

theorem part_085_1 : RS5.BandZeros ((55455704027 : ℝ) / 65536) ((55464564624 : ℝ) / 65536) 254 := by
  have g0 := band_0682
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0683
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55455704027 : ℝ) / 65536) ((55464564624 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_085_1 <;> assumption
