-- Prove2me | solution 1 for RH1E6S09.part_032_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:40:08.862243+00:00
-- url     : https://prove2.me/submissions/98a92f7a-0256-471d-9565-d754813a72cc

import Definitions.Def_RH1E6S09_D032_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0258 : RS5.BandZeros ((37228702743 : ℝ) / 65536) ((37233307216 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0258.s0 RH1E6S09_0258.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0258.s0 RH1E6S09_0258.rest = RH1E6S09_0258.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0258.s0 :: RH1E6S09_0258.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0258.s0.t = ((37228702743 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0258.s0]
  have e1 : RH1E6S09_0258.sL.t = ((37233307216 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0258.sL]
  rw [e0, e1] at h
  exact h

theorem band_0259 : RS5.BandZeros ((37233307216 : ℝ) / 65536) ((37237887690 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0259.s0 RH1E6S09_0259.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0259.s0 RH1E6S09_0259.rest = RH1E6S09_0259.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0259.s0 :: RH1E6S09_0259.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0259.s0.t = ((37233307216 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0259.s0]
  have e1 : RH1E6S09_0259.sL.t = ((37237887690 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0259.sL]
  rw [e0, e1] at h
  exact h

theorem part_032_1 : RS5.BandZeros ((37228702743 : ℝ) / 65536) ((37237887690 : ℝ) / 65536) 254 := by
  have g0 := band_0258
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0259
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37228702743 : ℝ) / 65536) ((37237887690 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_032_1 <;> assumption
