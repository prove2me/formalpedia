-- Prove2me | solution 1 for RH1E6S02.part_005_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:17:53.049642+00:00
-- url     : https://prove2.me/submissions/234002b1-ade6-4a90-83da-ece41364beb6

import Definitions.Def_RH1E6S02_D005_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0040 : RS5.BandZeros ((13308802318 : ℝ) / 65536) ((13313849828 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0040.s0 RH1E6S02_0040.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0040.s0 RH1E6S02_0040.rest = RH1E6S02_0040.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0040.s0 :: RH1E6S02_0040.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0040.s0.t = ((13308802318 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0040.s0]
  have e1 : RH1E6S02_0040.sL.t = ((13313849828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0040.sL]
  rw [e0, e1] at h
  exact h

theorem band_0041 : RS5.BandZeros ((13313849828 : ℝ) / 65536) ((13318881719 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0041.s0 RH1E6S02_0041.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0041.s0 RH1E6S02_0041.rest = RH1E6S02_0041.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0041.s0 :: RH1E6S02_0041.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0041.s0.t = ((13313849828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0041.s0]
  have e1 : RH1E6S02_0041.sL.t = ((13318881719 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0041.sL]
  rw [e0, e1] at h
  exact h

theorem part_005_0 : RS5.BandZeros ((13308802318 : ℝ) / 65536) ((13318881719 : ℝ) / 65536) 254 := by
  have g0 := band_0040
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0041
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((13308802318 : ℝ) / 65536) ((13318881719 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_005_0 <;> assumption
