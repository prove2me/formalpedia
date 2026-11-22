-- Prove2me | solution 1 for RH1E6S12.part_080_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:13:10.442279+00:00
-- url     : https://prove2.me/submissions/76bf72c3-9ead-409e-9b8e-1ec17df1ac3c

import Definitions.Def_RH1E6S12_D080_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0644 : RS5.BandZeros ((48765601768 : ℝ) / 65536) ((48770085522 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0644.s0 RH1E6S12_0644.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0644.s0 RH1E6S12_0644.rest = RH1E6S12_0644.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0644.s0 :: RH1E6S12_0644.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0644.s0.t = ((48765601768 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0644.s0]
  have e1 : RH1E6S12_0644.sL.t = ((48770085522 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0644.sL]
  rw [e0, e1] at h
  exact h

theorem band_0645 : RS5.BandZeros ((48770085522 : ℝ) / 65536) ((48774563624 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0645.s0 RH1E6S12_0645.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0645.s0 RH1E6S12_0645.rest = RH1E6S12_0645.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0645.s0 :: RH1E6S12_0645.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0645.s0.t = ((48770085522 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0645.s0]
  have e1 : RH1E6S12_0645.sL.t = ((48774563624 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0645.sL]
  rw [e0, e1] at h
  exact h

theorem part_080_2 : RS5.BandZeros ((48765601768 : ℝ) / 65536) ((48774563624 : ℝ) / 65536) 254 := by
  have g0 := band_0644
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0645
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48765601768 : ℝ) / 65536) ((48774563624 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_080_2 <;> assumption
