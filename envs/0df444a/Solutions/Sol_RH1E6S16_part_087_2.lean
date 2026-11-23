-- Prove2me | solution 1 for RH1E6S16.part_087_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:12:33.417624+00:00
-- url     : https://prove2.me/submissions/b0609293-89db-4a58-b128-53d05a6ab94f

import Definitions.Def_RH1E6S16_D087_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0700 : RS5.BandZeros ((62059139414 : ℝ) / 65536) ((62063516817 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0700.s0 RH1E6S16_0700.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0700.s0 RH1E6S16_0700.rest = RH1E6S16_0700.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0700.s0 :: RH1E6S16_0700.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0700.s0.t = ((62059139414 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0700.s0]
  have e1 : RH1E6S16_0700.sL.t = ((62063516817 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0700.sL]
  rw [e0, e1] at h
  exact h

theorem band_0701 : RS5.BandZeros ((62063516817 : ℝ) / 65536) ((62067887020 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0701.s0 RH1E6S16_0701.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0701.s0 RH1E6S16_0701.rest = RH1E6S16_0701.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0701.s0 :: RH1E6S16_0701.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0701.s0.t = ((62063516817 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0701.s0]
  have e1 : RH1E6S16_0701.sL.t = ((62067887020 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0701.sL]
  rw [e0, e1] at h
  exact h

theorem part_087_2 : RS5.BandZeros ((62059139414 : ℝ) / 65536) ((62067887020 : ℝ) / 65536) 254 := by
  have g0 := band_0700
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0701
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((62059139414 : ℝ) / 65536) ((62067887020 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_087_2 <;> assumption
