-- Prove2me | solution 1 for RH1E6S05.part_002_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:10:45.917363+00:00
-- url     : https://prove2.me/submissions/80683b49-ae18-4728-9117-29c51677b939

import Definitions.Def_RH1E6S05_D002_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0018 : RS5.BandZeros ((23023745025 : ℝ) / 65536) ((23028510037 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0018.s0 RH1E6S05_0018.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0018.s0 RH1E6S05_0018.rest = RH1E6S05_0018.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0018.s0 :: RH1E6S05_0018.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0018.s0.t = ((23023745025 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0018.s0]
  have e1 : RH1E6S05_0018.sL.t = ((23028510037 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0018.sL]
  rw [e0, e1] at h
  exact h

theorem band_0019 : RS5.BandZeros ((23028510037 : ℝ) / 65536) ((23033293794 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0019.s0 RH1E6S05_0019.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0019.s0 RH1E6S05_0019.rest = RH1E6S05_0019.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0019.s0 :: RH1E6S05_0019.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0019.s0.t = ((23028510037 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0019.s0]
  have e1 : RH1E6S05_0019.sL.t = ((23033293794 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0019.sL]
  rw [e0, e1] at h
  exact h

theorem part_002_1 : RS5.BandZeros ((23023745025 : ℝ) / 65536) ((23033293794 : ℝ) / 65536) 254 := by
  have g0 := band_0018
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0019
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((23023745025 : ℝ) / 65536) ((23033293794 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_002_1 <;> assumption
