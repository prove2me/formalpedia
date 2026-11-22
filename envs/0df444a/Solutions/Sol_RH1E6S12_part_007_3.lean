-- Prove2me | solution 1 for RH1E6S12.part_007_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:48:11.418876+00:00
-- url     : https://prove2.me/submissions/03a77252-31cd-45a3-8f2f-dc0906e1540f

import Definitions.Def_RH1E6S12_D007_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0062 : RS5.BandZeros ((46154159120 : ℝ) / 65536) ((46158642758 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0062.s0 RH1E6S12_0062.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0062.s0 RH1E6S12_0062.rest = RH1E6S12_0062.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0062.s0 :: RH1E6S12_0062.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0062.s0.t = ((46154159120 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0062.s0]
  have e1 : RH1E6S12_0062.sL.t = ((46158642758 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0062.sL]
  rw [e0, e1] at h
  exact h

theorem band_0063 : RS5.BandZeros ((46158642758 : ℝ) / 65536) ((46163146075 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0063.s0 RH1E6S12_0063.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0063.s0 RH1E6S12_0063.rest = RH1E6S12_0063.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0063.s0 :: RH1E6S12_0063.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0063.s0.t = ((46158642758 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0063.s0]
  have e1 : RH1E6S12_0063.sL.t = ((46163146075 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0063.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_3 : RS5.BandZeros ((46154159120 : ℝ) / 65536) ((46163146075 : ℝ) / 65536) 254 := by
  have g0 := band_0062
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0063
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46154159120 : ℝ) / 65536) ((46163146075 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_007_3 <;> assumption
