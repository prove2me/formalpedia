-- Prove2me | solution 1 for RH1E6S06.part_075_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:16:28.208612+00:00
-- url     : https://prove2.me/submissions/e9349ed5-0d7e-4143-a865-76c72a546c46

import Definitions.Def_RH1E6S06_D075_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0604 : RS5.BandZeros ((29056532317 : ℝ) / 65536) ((29061216782 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0604.s0 RH1E6S06_0604.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0604.s0 RH1E6S06_0604.rest = RH1E6S06_0604.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0604.s0 :: RH1E6S06_0604.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0604.s0.t = ((29056532317 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0604.s0]
  have e1 : RH1E6S06_0604.sL.t = ((29061216782 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0604.sL]
  rw [e0, e1] at h
  exact h

theorem band_0605 : RS5.BandZeros ((29061216782 : ℝ) / 65536) ((29065891633 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0605.s0 RH1E6S06_0605.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0605.s0 RH1E6S06_0605.rest = RH1E6S06_0605.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0605.s0 :: RH1E6S06_0605.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0605.s0.t = ((29061216782 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0605.s0]
  have e1 : RH1E6S06_0605.sL.t = ((29065891633 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0605.sL]
  rw [e0, e1] at h
  exact h

theorem part_075_2 : RS5.BandZeros ((29056532317 : ℝ) / 65536) ((29065891633 : ℝ) / 65536) 254 := by
  have g0 := band_0604
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0605
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((29056532317 : ℝ) / 65536) ((29065891633 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_075_2 <;> assumption
