-- Prove2me | solution 1 for RH1E6S03.part_048_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T07:00:02.159191+00:00
-- url     : https://prove2.me/submissions/57e80bc4-91a0-4f0c-904e-261af65f6b0b

import Definitions.Def_RH1E6S03_D048_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0386 : RS5.BandZeros ((18279886058 : ℝ) / 65536) ((18284801897 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0386.s0 RH1E6S03_0386.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0386.s0 RH1E6S03_0386.rest = RH1E6S03_0386.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0386.s0 :: RH1E6S03_0386.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0386.s0.t = ((18279886058 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0386.s0]
  have e1 : RH1E6S03_0386.sL.t = ((18284801897 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0386.sL]
  rw [e0, e1] at h
  exact h

theorem band_0387 : RS5.BandZeros ((18284801897 : ℝ) / 65536) ((18289688752 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0387.s0 RH1E6S03_0387.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0387.s0 RH1E6S03_0387.rest = RH1E6S03_0387.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0387.s0 :: RH1E6S03_0387.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0387.s0.t = ((18284801897 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0387.s0]
  have e1 : RH1E6S03_0387.sL.t = ((18289688752 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0387.sL]
  rw [e0, e1] at h
  exact h

theorem part_048_1 : RS5.BandZeros ((18279886058 : ℝ) / 65536) ((18289688752 : ℝ) / 65536) 254 := by
  have g0 := band_0386
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0387
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18279886058 : ℝ) / 65536) ((18289688752 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_048_1 <;> assumption
