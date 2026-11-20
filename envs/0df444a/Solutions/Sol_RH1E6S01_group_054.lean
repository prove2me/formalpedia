-- Prove2me | solution 1 for RH1E6S01.group_054
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:20:23.106285+00:00
-- url     : https://prove2.me/submissions/af0b5bdb-a6b7-40ac-8162-09093f0792db

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S01_part_054_0
import Theorems.Thm_RH1E6S01_part_054_1
import Theorems.Thm_RH1E6S01_part_054_2
import Theorems.Thm_RH1E6S01_part_054_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem group_054 : RS5.BandZeros ((12048380140 : ℝ) / 65536) ((12089034583 : ℝ) / 65536) 1016 := by
  have g0 := part_054_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_054_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_054_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_054_3
  exact g3
end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12048380140 : ℝ) / 65536) ((12089034583 : ℝ) / 65536) 1016 := by
  apply RH1E6S01.group_054 <;> assumption
