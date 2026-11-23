-- Prove2me | solution 1 for RH1E6S13.part_088_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:07:55.428736+00:00
-- url     : https://prove2.me/submissions/6a2c12bf-7450-42d7-b94b-3c3a9158b883

import Definitions.Def_RH1E6S13_D088_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0704 : RS5.BandZeros ((52292975313 : ℝ) / 65536) ((52297434011 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0704.s0 RH1E6S13_0704.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0704.s0 RH1E6S13_0704.rest = RH1E6S13_0704.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0704.s0 :: RH1E6S13_0704.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0704.s0.t = ((52292975313 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0704.s0]
  have e1 : RH1E6S13_0704.sL.t = ((52297434011 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0704.sL]
  rw [e0, e1] at h
  exact h

theorem band_0705 : RS5.BandZeros ((52297434011 : ℝ) / 65536) ((52301866398 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0705.s0 RH1E6S13_0705.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0705.s0 RH1E6S13_0705.rest = RH1E6S13_0705.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0705.s0 :: RH1E6S13_0705.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0705.s0.t = ((52297434011 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0705.s0]
  have e1 : RH1E6S13_0705.sL.t = ((52301866398 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0705.sL]
  rw [e0, e1] at h
  exact h

theorem part_088_0 : RS5.BandZeros ((52292975313 : ℝ) / 65536) ((52301866398 : ℝ) / 65536) 254 := by
  have g0 := band_0704
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0705
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((52292975313 : ℝ) / 65536) ((52301866398 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_088_0 <;> assumption
