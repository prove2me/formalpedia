-- Prove2me | solution 1 for RH1E6S02.part_037_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:27:29.074846+00:00
-- url     : https://prove2.me/submissions/de8266f8-a996-48f5-89f4-bd73bc3c0374

import Definitions.Def_RH1E6S02_D037_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0296 : RS5.BandZeros ((14592350500 : ℝ) / 65536) ((14597344654 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0296.s0 RH1E6S02_0296.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0296.s0 RH1E6S02_0296.rest = RH1E6S02_0296.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0296.s0 :: RH1E6S02_0296.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0296.s0.t = ((14592350500 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0296.s0]
  have e1 : RH1E6S02_0296.sL.t = ((14597344654 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0296.sL]
  rw [e0, e1] at h
  exact h

theorem band_0297 : RS5.BandZeros ((14597344654 : ℝ) / 65536) ((14602332839 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0297.s0 RH1E6S02_0297.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0297.s0 RH1E6S02_0297.rest = RH1E6S02_0297.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0297.s0 :: RH1E6S02_0297.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0297.s0.t = ((14597344654 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0297.s0]
  have e1 : RH1E6S02_0297.sL.t = ((14602332839 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0297.sL]
  rw [e0, e1] at h
  exact h

theorem part_037_0 : RS5.BandZeros ((14592350500 : ℝ) / 65536) ((14602332839 : ℝ) / 65536) 254 := by
  have g0 := band_0296
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0297
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((14592350500 : ℝ) / 65536) ((14602332839 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_037_0 <;> assumption
