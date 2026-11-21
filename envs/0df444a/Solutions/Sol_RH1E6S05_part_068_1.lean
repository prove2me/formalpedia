-- Prove2me | solution 1 for RH1E6S05.part_068_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T16:00:17.020738+00:00
-- url     : https://prove2.me/submissions/d04f496c-94a9-4984-9f16-cec2a81bfcb6

import Definitions.Def_RH1E6S05_D068_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0546 : RS5.BandZeros ((25537492043 : ℝ) / 65536) ((25542230974 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0546.s0 RH1E6S05_0546.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0546.s0 RH1E6S05_0546.rest = RH1E6S05_0546.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0546.s0 :: RH1E6S05_0546.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0546.s0.t = ((25537492043 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0546.s0]
  have e1 : RH1E6S05_0546.sL.t = ((25542230974 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0546.sL]
  rw [e0, e1] at h
  exact h

theorem band_0547 : RS5.BandZeros ((25542230974 : ℝ) / 65536) ((25546988482 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0547.s0 RH1E6S05_0547.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0547.s0 RH1E6S05_0547.rest = RH1E6S05_0547.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0547.s0 :: RH1E6S05_0547.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0547.s0.t = ((25542230974 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0547.s0]
  have e1 : RH1E6S05_0547.sL.t = ((25546988482 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0547.sL]
  rw [e0, e1] at h
  exact h

theorem part_068_1 : RS5.BandZeros ((25537492043 : ℝ) / 65536) ((25546988482 : ℝ) / 65536) 254 := by
  have g0 := band_0546
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0547
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25537492043 : ℝ) / 65536) ((25546988482 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_068_1 <;> assumption
