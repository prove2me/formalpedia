-- Prove2me | solution 1 for RH1E6S09.part_026_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:23:28.073092+00:00
-- url     : https://prove2.me/submissions/b5b30aaf-0e1d-448d-a7eb-4c88c90c4b21

import Definitions.Def_RH1E6S09_D026_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0208 : RS5.BandZeros ((36999528153 : ℝ) / 65536) ((37004107380 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0208.s0 RH1E6S09_0208.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0208.s0 RH1E6S09_0208.rest = RH1E6S09_0208.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0208.s0 :: RH1E6S09_0208.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0208.s0.t = ((36999528153 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0208.s0]
  have e1 : RH1E6S09_0208.sL.t = ((37004107380 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0208.sL]
  rw [e0, e1] at h
  exact h

theorem band_0209 : RS5.BandZeros ((37004107380 : ℝ) / 65536) ((37008701259 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0209.s0 RH1E6S09_0209.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0209.s0 RH1E6S09_0209.rest = RH1E6S09_0209.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0209.s0 :: RH1E6S09_0209.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0209.s0.t = ((37004107380 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0209.s0]
  have e1 : RH1E6S09_0209.sL.t = ((37008701259 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0209.sL]
  rw [e0, e1] at h
  exact h

theorem part_026_0 : RS5.BandZeros ((36999528153 : ℝ) / 65536) ((37008701259 : ℝ) / 65536) 254 := by
  have g0 := band_0208
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0209
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36999528153 : ℝ) / 65536) ((37008701259 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_026_0 <;> assumption
