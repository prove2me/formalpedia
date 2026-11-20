-- Prove2me | solution 1 for RH1E6S03.part_007_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:31:23.220205+00:00
-- url     : https://prove2.me/submissions/6443ab4d-4528-480c-9282-a580ec5ad21e

import Definitions.Def_RH1E6S03_D007_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0056 : RS5.BandZeros ((16660279630 : ℝ) / 65536) ((16665189932 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0056.s0 RH1E6S03_0056.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0056.s0 RH1E6S03_0056.rest = RH1E6S03_0056.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0056.s0 :: RH1E6S03_0056.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0056.s0.t = ((16660279630 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0056.s0]
  have e1 : RH1E6S03_0056.sL.t = ((16665189932 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0056.sL]
  rw [e0, e1] at h
  exact h

theorem band_0057 : RS5.BandZeros ((16665189932 : ℝ) / 65536) ((16670138914 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0057.s0 RH1E6S03_0057.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0057.s0 RH1E6S03_0057.rest = RH1E6S03_0057.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0057.s0 :: RH1E6S03_0057.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0057.s0.t = ((16665189932 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0057.s0]
  have e1 : RH1E6S03_0057.sL.t = ((16670138914 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0057.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_0 : RS5.BandZeros ((16660279630 : ℝ) / 65536) ((16670138914 : ℝ) / 65536) 254 := by
  have g0 := band_0056
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0057
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((16660279630 : ℝ) / 65536) ((16670138914 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_007_0 <;> assumption
