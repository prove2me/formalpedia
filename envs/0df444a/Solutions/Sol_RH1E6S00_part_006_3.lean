-- Prove2me | solution 1 for RH1E6S00.part_006_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:02:35.356087+00:00
-- url     : https://prove2.me/submissions/8f9b10ec-0475-4029-899a-4095e776e00a

import Definitions.Def_RH1E6S00_D006_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0054 : RS5.BandZeros ((6844839487 : ℝ) / 65536) ((6850230861 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0054.s0 RH1E6S00_0054.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0054.s0 RH1E6S00_0054.rest = RH1E6S00_0054.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0054.s0 :: RH1E6S00_0054.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0054.s0.t = ((6844839487 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0054.s0]
  have e1 : RH1E6S00_0054.sL.t = ((6850230861 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0054.sL]
  rw [e0, e1] at h
  exact h

theorem band_0055 : RS5.BandZeros ((6850230861 : ℝ) / 65536) ((6855600617 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0055.s0 RH1E6S00_0055.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0055.s0 RH1E6S00_0055.rest = RH1E6S00_0055.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0055.s0 :: RH1E6S00_0055.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0055.s0.t = ((6850230861 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0055.s0]
  have e1 : RH1E6S00_0055.sL.t = ((6855600617 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0055.sL]
  rw [e0, e1] at h
  exact h

theorem part_006_3 : RS5.BandZeros ((6844839487 : ℝ) / 65536) ((6855600617 : ℝ) / 65536) 254 := by
  have g0 := band_0054
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0055
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((6844839487 : ℝ) / 65536) ((6855600617 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_006_3 <;> assumption
