-- Prove2me | solution 1 for RH1E6S16.part_000_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:50:46.377797+00:00
-- url     : https://prove2.me/submissions/c4435d0d-7e6e-4c99-b0e7-66fda0a87f24

import Definitions.Def_RH1E6S16_D000_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0002 : RS5.BandZeros ((58991194418 : ℝ) / 65536) ((58995605256 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0002.s0 RH1E6S16_0002.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0002.s0 RH1E6S16_0002.rest = RH1E6S16_0002.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0002.s0 :: RH1E6S16_0002.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0002.s0.t = ((58991194418 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0002.s0]
  have e1 : RH1E6S16_0002.sL.t = ((58995605256 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0002.sL]
  rw [e0, e1] at h
  exact h

theorem band_0003 : RS5.BandZeros ((58995605256 : ℝ) / 65536) ((58999998732 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0003.s0 RH1E6S16_0003.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0003.s0 RH1E6S16_0003.rest = RH1E6S16_0003.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0003.s0 :: RH1E6S16_0003.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0003.s0.t = ((58995605256 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0003.s0]
  have e1 : RH1E6S16_0003.sL.t = ((58999998732 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0003.sL]
  rw [e0, e1] at h
  exact h

theorem part_000_1 : RS5.BandZeros ((58991194418 : ℝ) / 65536) ((58999998732 : ℝ) / 65536) 254 := by
  have g0 := band_0002
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0003
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((58991194418 : ℝ) / 65536) ((58999998732 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_000_1 <;> assumption
