-- Prove2me | solution 1 for RH1E6S12.part_007_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:45:30.273316+00:00
-- url     : https://prove2.me/submissions/f0c4440e-db03-4670-a55d-8ee2f6c043ae

import Definitions.Def_RH1E6S12_D007_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0060 : RS5.BandZeros ((46145145842 : ℝ) / 65536) ((46149643646 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0060.s0 RH1E6S12_0060.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0060.s0 RH1E6S12_0060.rest = RH1E6S12_0060.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0060.s0 :: RH1E6S12_0060.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0060.s0.t = ((46145145842 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0060.s0]
  have e1 : RH1E6S12_0060.sL.t = ((46149643646 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0060.sL]
  rw [e0, e1] at h
  exact h

theorem band_0061 : RS5.BandZeros ((46149643646 : ℝ) / 65536) ((46154159120 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0061.s0 RH1E6S12_0061.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0061.s0 RH1E6S12_0061.rest = RH1E6S12_0061.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0061.s0 :: RH1E6S12_0061.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0061.s0.t = ((46149643646 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0061.s0]
  have e1 : RH1E6S12_0061.sL.t = ((46154159120 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0061.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_2 : RS5.BandZeros ((46145145842 : ℝ) / 65536) ((46154159120 : ℝ) / 65536) 254 := by
  have g0 := band_0060
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0061
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46145145842 : ℝ) / 65536) ((46154159120 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_007_2 <;> assumption
