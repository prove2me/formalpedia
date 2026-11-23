-- Prove2me | solution 1 for RH1E6S14.part_003_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:37:02.933029+00:00
-- url     : https://prove2.me/submissions/18c0c210-748b-4d50-b31e-cb9a8b845be2

import Definitions.Def_RH1E6S14_D003_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0030 : RS5.BandZeros ((52562224910 : ℝ) / 65536) ((52566697545 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0030.s0 RH1E6S14_0030.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0030.s0 RH1E6S14_0030.rest = RH1E6S14_0030.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0030.s0 :: RH1E6S14_0030.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0030.s0.t = ((52562224910 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0030.s0]
  have e1 : RH1E6S14_0030.sL.t = ((52566697545 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0030.sL]
  rw [e0, e1] at h
  exact h

theorem band_0031 : RS5.BandZeros ((52566697545 : ℝ) / 65536) ((52571141307 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0031.s0 RH1E6S14_0031.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0031.s0 RH1E6S14_0031.rest = RH1E6S14_0031.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0031.s0 :: RH1E6S14_0031.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0031.s0.t = ((52566697545 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0031.s0]
  have e1 : RH1E6S14_0031.sL.t = ((52571141307 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0031.sL]
  rw [e0, e1] at h
  exact h

theorem part_003_3 : RS5.BandZeros ((52562224910 : ℝ) / 65536) ((52571141307 : ℝ) / 65536) 254 := by
  have g0 := band_0030
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0031
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((52562224910 : ℝ) / 65536) ((52571141307 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_003_3 <;> assumption
