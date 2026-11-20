-- Prove2me | solution 1 for RH1E6S00.part_071_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:11:12.095562+00:00
-- url     : https://prove2.me/submissions/2066b5f8-d6e3-4cdd-b495-570bb7653c96

import Definitions.Def_RH1E6S00_D071_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0570 : RS5.BandZeros ((9571767011 : ℝ) / 65536) ((9576978638 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0570.s0 RH1E6S00_0570.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0570.s0 RH1E6S00_0570.rest = RH1E6S00_0570.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0570.s0 :: RH1E6S00_0570.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0570.s0.t = ((9571767011 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0570.s0]
  have e1 : RH1E6S00_0570.sL.t = ((9576978638 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0570.sL]
  rw [e0, e1] at h
  exact h

theorem band_0571 : RS5.BandZeros ((9576978638 : ℝ) / 65536) ((9582179746 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0571.s0 RH1E6S00_0571.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0571.s0 RH1E6S00_0571.rest = RH1E6S00_0571.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0571.s0 :: RH1E6S00_0571.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0571.s0.t = ((9576978638 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0571.s0]
  have e1 : RH1E6S00_0571.sL.t = ((9582179746 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0571.sL]
  rw [e0, e1] at h
  exact h

theorem part_071_1 : RS5.BandZeros ((9571767011 : ℝ) / 65536) ((9582179746 : ℝ) / 65536) 254 := by
  have g0 := band_0570
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0571
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9571767011 : ℝ) / 65536) ((9582179746 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_071_1 <;> assumption
