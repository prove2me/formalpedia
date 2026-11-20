-- Prove2me | solution 1 for RH1E6S02.part_009_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T02:27:19.937187+00:00
-- url     : https://prove2.me/submissions/2b86f98c-9122-40cd-8e42-ef8a1ad7916c

import Definitions.Def_RH1E6S02_D009_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0074 : RS5.BandZeros ((13479937845 : ℝ) / 65536) ((13484969177 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0074.s0 RH1E6S02_0074.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0074.s0 RH1E6S02_0074.rest = RH1E6S02_0074.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0074.s0 :: RH1E6S02_0074.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0074.s0.t = ((13479937845 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0074.s0]
  have e1 : RH1E6S02_0074.sL.t = ((13484969177 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0074.sL]
  rw [e0, e1] at h
  exact h

theorem band_0075 : RS5.BandZeros ((13484969177 : ℝ) / 65536) ((13490009586 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0075.s0 RH1E6S02_0075.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0075.s0 RH1E6S02_0075.rest = RH1E6S02_0075.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0075.s0 :: RH1E6S02_0075.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0075.s0.t = ((13484969177 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0075.s0]
  have e1 : RH1E6S02_0075.sL.t = ((13490009586 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0075.sL]
  rw [e0, e1] at h
  exact h

theorem part_009_1 : RS5.BandZeros ((13479937845 : ℝ) / 65536) ((13490009586 : ℝ) / 65536) 254 := by
  have g0 := band_0074
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0075
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((13479937845 : ℝ) / 65536) ((13490009586 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_009_1 <;> assumption
