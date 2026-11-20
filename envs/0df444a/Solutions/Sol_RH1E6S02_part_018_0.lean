-- Prove2me | solution 1 for RH1E6S02.part_018_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:46:28.992799+00:00
-- url     : https://prove2.me/submissions/c5132cde-908a-467a-a1cd-e7fc366590ca

import Definitions.Def_RH1E6S02_D018_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0144 : RS5.BandZeros ((13831619256 : ℝ) / 65536) ((13836655105 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0144.s0 RH1E6S02_0144.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0144.s0 RH1E6S02_0144.rest = RH1E6S02_0144.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0144.s0 :: RH1E6S02_0144.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0144.s0.t = ((13831619256 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0144.s0]
  have e1 : RH1E6S02_0144.sL.t = ((13836655105 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0144.sL]
  rw [e0, e1] at h
  exact h

theorem band_0145 : RS5.BandZeros ((13836655105 : ℝ) / 65536) ((13841655803 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0145.s0 RH1E6S02_0145.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0145.s0 RH1E6S02_0145.rest = RH1E6S02_0145.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0145.s0 :: RH1E6S02_0145.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0145.s0.t = ((13836655105 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0145.s0]
  have e1 : RH1E6S02_0145.sL.t = ((13841655803 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0145.sL]
  rw [e0, e1] at h
  exact h

theorem part_018_0 : RS5.BandZeros ((13831619256 : ℝ) / 65536) ((13841655803 : ℝ) / 65536) 254 := by
  have g0 := band_0144
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0145
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((13831619256 : ℝ) / 65536) ((13841655803 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_018_0 <;> assumption
