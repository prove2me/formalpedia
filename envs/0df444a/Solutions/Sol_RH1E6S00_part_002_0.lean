-- Prove2me | solution 1 for RH1E6S00.part_002_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T20:53:17.488549+00:00
-- url     : https://prove2.me/submissions/e47750ae-2bf1-4cef-811d-28b19f6c0383

import Definitions.Def_RH1E6S00_D002_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0016 : RS5.BandZeros ((6640043049 : ℝ) / 65536) ((6645440694 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0016.s0 RH1E6S00_0016.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0016.s0 RH1E6S00_0016.rest = RH1E6S00_0016.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0016.s0 :: RH1E6S00_0016.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0016.s0.t = ((6640043049 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0016.s0]
  have e1 : RH1E6S00_0016.sL.t = ((6645440694 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0016.sL]
  rw [e0, e1] at h
  exact h

theorem band_0017 : RS5.BandZeros ((6645440694 : ℝ) / 65536) ((6650848511 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0017.s0 RH1E6S00_0017.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0017.s0 RH1E6S00_0017.rest = RH1E6S00_0017.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0017.s0 :: RH1E6S00_0017.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0017.s0.t = ((6645440694 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0017.s0]
  have e1 : RH1E6S00_0017.sL.t = ((6650848511 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0017.sL]
  rw [e0, e1] at h
  exact h

theorem part_002_0 : RS5.BandZeros ((6640043049 : ℝ) / 65536) ((6650848511 : ℝ) / 65536) 254 := by
  have g0 := band_0016
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0017
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((6640043049 : ℝ) / 65536) ((6650848511 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_002_0 <;> assumption
