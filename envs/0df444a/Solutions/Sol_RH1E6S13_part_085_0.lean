-- Prove2me | solution 1 for RH1E6S13.part_085_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:01:46.673811+00:00
-- url     : https://prove2.me/submissions/8ef44cee-12c3-4cef-a6e2-1882c403999a

import Definitions.Def_RH1E6S13_D085_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0680 : RS5.BandZeros ((52186158352 : ℝ) / 65536) ((52190617826 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0680.s0 RH1E6S13_0680.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0680.s0 RH1E6S13_0680.rest = RH1E6S13_0680.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0680.s0 :: RH1E6S13_0680.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0680.s0.t = ((52186158352 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0680.s0]
  have e1 : RH1E6S13_0680.sL.t = ((52190617826 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0680.sL]
  rw [e0, e1] at h
  exact h

theorem band_0681 : RS5.BandZeros ((52190617826 : ℝ) / 65536) ((52195059746 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0681.s0 RH1E6S13_0681.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0681.s0 RH1E6S13_0681.rest = RH1E6S13_0681.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0681.s0 :: RH1E6S13_0681.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0681.s0.t = ((52190617826 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0681.s0]
  have e1 : RH1E6S13_0681.sL.t = ((52195059746 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0681.sL]
  rw [e0, e1] at h
  exact h

theorem part_085_0 : RS5.BandZeros ((52186158352 : ℝ) / 65536) ((52195059746 : ℝ) / 65536) 254 := by
  have g0 := band_0680
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0681
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((52186158352 : ℝ) / 65536) ((52195059746 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_085_0 <;> assumption
