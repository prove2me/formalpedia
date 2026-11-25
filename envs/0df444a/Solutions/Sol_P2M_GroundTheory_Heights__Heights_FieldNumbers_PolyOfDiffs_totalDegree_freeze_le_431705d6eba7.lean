-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_freeze_le_431705d6eba7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:53:10.403676+00:00
-- url     : https://prove2.me/submissions/a6d44dbf-189a-4afb-8c87-00d477bd0b06

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
open GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
variable {K : Type}
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
theorem _root_.solution (s : Finset K) (N : K → ℚ) (j : K) :
    (freeze s N j).totalDegree ≤ 1 := by
  unfold freeze
  split_ifs
  · exact (totalDegree_X j).le
  · rw [totalDegree_C]; exact zero_le_one
end GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
