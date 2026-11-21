-- Prove2me | solution 1 for RH1E6S08.part_022_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:57:27.876451+00:00
-- url     : https://prove2.me/submissions/db8d3ae6-0952-4b70-b008-2b6c6335be87

import Definitions.Def_RH1E6S08_D022_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0182 : RS5.BandZeros ((33610519015 : ℝ) / 65536) ((33615117913 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0182.s0 RH1E6S08_0182.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0182.s0 RH1E6S08_0182.rest = RH1E6S08_0182.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0182.s0 :: RH1E6S08_0182.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0182.s0.t = ((33610519015 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0182.s0]
  have e1 : RH1E6S08_0182.sL.t = ((33615117913 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0182.sL]
  rw [e0, e1] at h
  exact h

theorem band_0183 : RS5.BandZeros ((33615117913 : ℝ) / 65536) ((33619759678 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0183.s0 RH1E6S08_0183.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0183.s0 RH1E6S08_0183.rest = RH1E6S08_0183.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0183.s0 :: RH1E6S08_0183.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0183.s0.t = ((33615117913 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0183.s0]
  have e1 : RH1E6S08_0183.sL.t = ((33619759678 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0183.sL]
  rw [e0, e1] at h
  exact h

theorem part_022_3 : RS5.BandZeros ((33610519015 : ℝ) / 65536) ((33619759678 : ℝ) / 65536) 254 := by
  have g0 := band_0182
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0183
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33610519015 : ℝ) / 65536) ((33619759678 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_022_3 <;> assumption
