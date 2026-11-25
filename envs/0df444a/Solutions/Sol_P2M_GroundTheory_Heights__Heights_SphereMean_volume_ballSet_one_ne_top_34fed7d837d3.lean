-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_one_ne_top_34fed7d837d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:08.53635+00:00
-- url     : https://prove2.me/submissions/c4a5f485-3ad1-4461-b683-d9a9d3bc9bec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_ballSet_subset_closedBall_a60a8a60db99

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution (n : ℕ) : volume (ballSet n 1) ≠ ⊤ :=
  (measure_mono (ballSet_subset_closedBall n)).trans_lt measure_closedBall_lt_top |>.ne
end GroundTheory.Heights₂.Heights.SphereMean
