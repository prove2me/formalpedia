-- Prove2me | solution 1 for RH1E6S00.part_068_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:04:14.470078+00:00
-- url     : https://prove2.me/submissions/4c328d9f-dd10-46e6-89fb-57a4a1f46ec2

import Definitions.Def_RH1E6S00_D068_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0548 : RS5.BandZeros ((9457254723 : ℝ) / 65536) ((9462472595 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0548.s0 RH1E6S00_0548.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0548.s0 RH1E6S00_0548.rest = RH1E6S00_0548.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0548.s0 :: RH1E6S00_0548.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0548.s0.t = ((9457254723 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0548.s0]
  have e1 : RH1E6S00_0548.sL.t = ((9462472595 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0548.sL]
  rw [e0, e1] at h
  exact h

theorem band_0549 : RS5.BandZeros ((9462472595 : ℝ) / 65536) ((9467690180 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0549.s0 RH1E6S00_0549.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0549.s0 RH1E6S00_0549.rest = RH1E6S00_0549.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0549.s0 :: RH1E6S00_0549.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0549.s0.t = ((9462472595 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0549.s0]
  have e1 : RH1E6S00_0549.sL.t = ((9467690180 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0549.sL]
  rw [e0, e1] at h
  exact h

theorem part_068_2 : RS5.BandZeros ((9457254723 : ℝ) / 65536) ((9467690180 : ℝ) / 65536) 254 := by
  have g0 := band_0548
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0549
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9457254723 : ℝ) / 65536) ((9467690180 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_068_2 <;> assumption
