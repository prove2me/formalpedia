-- Prove2me | solution 1 for RH1E6S12.part_085_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:27:45.407668+00:00
-- url     : https://prove2.me/submissions/5c4f151e-69be-470b-b703-076b32bf2578

import Definitions.Def_RH1E6S12_D085_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0686 : RS5.BandZeros ((48953586523 : ℝ) / 65536) ((48958054134 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0686.s0 RH1E6S12_0686.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0686.s0 RH1E6S12_0686.rest = RH1E6S12_0686.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0686.s0 :: RH1E6S12_0686.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0686.s0.t = ((48953586523 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0686.s0]
  have e1 : RH1E6S12_0686.sL.t = ((48958054134 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0686.sL]
  rw [e0, e1] at h
  exact h

theorem band_0687 : RS5.BandZeros ((48958054134 : ℝ) / 65536) ((48962532956 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0687.s0 RH1E6S12_0687.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0687.s0 RH1E6S12_0687.rest = RH1E6S12_0687.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0687.s0 :: RH1E6S12_0687.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0687.s0.t = ((48958054134 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0687.s0]
  have e1 : RH1E6S12_0687.sL.t = ((48962532956 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0687.sL]
  rw [e0, e1] at h
  exact h

theorem part_085_3 : RS5.BandZeros ((48953586523 : ℝ) / 65536) ((48962532956 : ℝ) / 65536) 254 := by
  have g0 := band_0686
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0687
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48953586523 : ℝ) / 65536) ((48962532956 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_085_3 <;> assumption
