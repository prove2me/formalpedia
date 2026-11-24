-- Prove2me | solution 1 for RH1E6S17.part_092_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:40:49.886882+00:00
-- url     : https://prove2.me/submissions/86b9417b-89b9-465b-8051-544ab94fb76c

import Definitions.Def_RH1E6S17_D092_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0738 : RS5.BandZeros ((65488332262 : ℝ) / 65536) ((65492681413 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0738.s0 RH1E6S17_0738.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0738.s0 RH1E6S17_0738.rest = RH1E6S17_0738.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0738.s0 :: RH1E6S17_0738.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0738.s0.t = ((65488332262 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0738.s0]
  have e1 : RH1E6S17_0738.sL.t = ((65492681413 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0738.sL]
  rw [e0, e1] at h
  exact h

theorem band_0739 : RS5.BandZeros ((65492681413 : ℝ) / 65536) ((65497064920 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0739.s0 RH1E6S17_0739.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0739.s0 RH1E6S17_0739.rest = RH1E6S17_0739.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0739.s0 :: RH1E6S17_0739.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0739.s0.t = ((65492681413 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0739.s0]
  have e1 : RH1E6S17_0739.sL.t = ((65497064920 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0739.sL]
  rw [e0, e1] at h
  exact h

theorem part_092_1 : RS5.BandZeros ((65488332262 : ℝ) / 65536) ((65497064920 : ℝ) / 65536) 254 := by
  have g0 := band_0738
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0739
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65488332262 : ℝ) / 65536) ((65497064920 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_092_1 <;> assumption
