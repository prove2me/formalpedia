-- Prove2me | solution 1 for RH1E6S05.part_005_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:18:18.638145+00:00
-- url     : https://prove2.me/submissions/4e96b9ab-0808-4b17-b49d-16193c03856d

import Definitions.Def_RH1E6S05_D005_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0044 : RS5.BandZeros ((23148076731 : ℝ) / 65536) ((23152848810 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0044.s0 RH1E6S05_0044.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0044.s0 RH1E6S05_0044.rest = RH1E6S05_0044.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0044.s0 :: RH1E6S05_0044.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0044.s0.t = ((23148076731 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0044.s0]
  have e1 : RH1E6S05_0044.sL.t = ((23152848810 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0044.sL]
  rw [e0, e1] at h
  exact h

theorem band_0045 : RS5.BandZeros ((23152848810 : ℝ) / 65536) ((23157639624 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0045.s0 RH1E6S05_0045.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0045.s0 RH1E6S05_0045.rest = RH1E6S05_0045.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0045.s0 :: RH1E6S05_0045.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0045.s0.t = ((23152848810 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0045.s0]
  have e1 : RH1E6S05_0045.sL.t = ((23157639624 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0045.sL]
  rw [e0, e1] at h
  exact h

theorem part_005_2 : RS5.BandZeros ((23148076731 : ℝ) / 65536) ((23157639624 : ℝ) / 65536) 254 := by
  have g0 := band_0044
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0045
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((23148076731 : ℝ) / 65536) ((23157639624 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_005_2 <;> assumption
