-- Prove2me | solution 1 for RH1E6S03.part_082_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T08:21:04.420151+00:00
-- url     : https://prove2.me/submissions/c78d78b2-16e0-4f86-8f24-74ba769cf635

import Definitions.Def_RH1E6S03_D082_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0662 : RS5.BandZeros ((19624227525 : ℝ) / 65536) ((19629082314 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0662.s0 RH1E6S03_0662.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0662.s0 RH1E6S03_0662.rest = RH1E6S03_0662.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0662.s0 :: RH1E6S03_0662.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0662.s0.t = ((19624227525 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0662.s0]
  have e1 : RH1E6S03_0662.sL.t = ((19629082314 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0662.sL]
  rw [e0, e1] at h
  exact h

theorem band_0663 : RS5.BandZeros ((19629082314 : ℝ) / 65536) ((19633946547 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0663.s0 RH1E6S03_0663.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0663.s0 RH1E6S03_0663.rest = RH1E6S03_0663.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0663.s0 :: RH1E6S03_0663.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0663.s0.t = ((19629082314 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0663.s0]
  have e1 : RH1E6S03_0663.sL.t = ((19633946547 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0663.sL]
  rw [e0, e1] at h
  exact h

theorem part_082_3 : RS5.BandZeros ((19624227525 : ℝ) / 65536) ((19633946547 : ℝ) / 65536) 254 := by
  have g0 := band_0662
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0663
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((19624227525 : ℝ) / 65536) ((19633946547 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_082_3 <;> assumption
