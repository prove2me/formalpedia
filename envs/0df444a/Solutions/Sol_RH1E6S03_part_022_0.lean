-- Prove2me | solution 1 for RH1E6S03.part_022_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:03:20.954466+00:00
-- url     : https://prove2.me/submissions/5465f387-8744-4542-92e8-e8df07ec3a4b

import Definitions.Def_RH1E6S03_D022_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0176 : RS5.BandZeros ((17250877819 : ℝ) / 65536) ((17255791397 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0176.s0 RH1E6S03_0176.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0176.s0 RH1E6S03_0176.rest = RH1E6S03_0176.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0176.s0 :: RH1E6S03_0176.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0176.s0.t = ((17250877819 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0176.s0]
  have e1 : RH1E6S03_0176.sL.t = ((17255791397 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0176.sL]
  rw [e0, e1] at h
  exact h

theorem band_0177 : RS5.BandZeros ((17255791397 : ℝ) / 65536) ((17260714515 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0177.s0 RH1E6S03_0177.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0177.s0 RH1E6S03_0177.rest = RH1E6S03_0177.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0177.s0 :: RH1E6S03_0177.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0177.s0.t = ((17255791397 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0177.s0]
  have e1 : RH1E6S03_0177.sL.t = ((17260714515 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0177.sL]
  rw [e0, e1] at h
  exact h

theorem part_022_0 : RS5.BandZeros ((17250877819 : ℝ) / 65536) ((17260714515 : ℝ) / 65536) 254 := by
  have g0 := band_0176
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0177
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17250877819 : ℝ) / 65536) ((17260714515 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_022_0 <;> assumption
