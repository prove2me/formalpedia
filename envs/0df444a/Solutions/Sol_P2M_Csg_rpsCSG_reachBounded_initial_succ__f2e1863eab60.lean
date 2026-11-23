-- Prove2me | solution 1 for P2M_Csg_rpsCSG_reachBounded_initial_succ__f2e1863eab60
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:34:48.164961+00:00
-- url     : https://prove2.me/submissions/fcf013ea-f3b6-47a8-96a2-f41bd851de79

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_rpsCSG_reachBounded_win1
import Theorems.Thm_Csg_rpsCSG_reachBounded_initial_succ

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (k : ℕ) :
    rpsCSG.reachBounded rpsGoalWin2 (k + 1) .initial =
      (1 + rpsCSG.reachBounded rpsGoalWin2 k .draw) / 3 := by
  rw [rpsCSG_reachBounded_initial_succ, rpsCSG_reachBounded_win1]
  ring
end Csg
