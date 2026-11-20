-- Prove2me | solution 1 for RH1E6S01.group_059
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:29:52.623301+00:00
-- url     : https://prove2.me/submissions/2e8dbec6-4c17-46f0-a2e1-6e2ec48f9390

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S01_part_059_0
import Theorems.Thm_RH1E6S01_part_059_1
import Theorems.Thm_RH1E6S01_part_059_2
import Theorems.Thm_RH1E6S01_part_059_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem group_059 : RS5.BandZeros ((12251620009 : ℝ) / 65536) ((12292208562 : ℝ) / 65536) 1016 := by
  have g0 := part_059_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_059_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_059_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_059_3
  exact g3
end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12251620009 : ℝ) / 65536) ((12292208562 : ℝ) / 65536) 1016 := by
  apply RH1E6S01.group_059 <;> assumption
