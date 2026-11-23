-- Prove2me | solution 1 for RH1E6S15.group_092
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:59:38.915573+00:00
-- url     : https://prove2.me/submissions/ec20afa5-6f8a-491a-b484-55d42a658563

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S15_part_092_0
import Theorems.Thm_RH1E6S15_part_092_1
import Theorems.Thm_RH1E6S15_part_092_2
import Theorems.Thm_RH1E6S15_part_092_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem group_092 : RS5.BandZeros ((58955345706 : ℝ) / 65536) ((58982400000 : ℝ) / 65536) 780 := by
  have g0 := part_092_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_092_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_092_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_092_3
  exact g3
end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58955345706 : ℝ) / 65536) ((58982400000 : ℝ) / 65536) 780 := by
  apply RH1E6S15.group_092 <;> assumption
