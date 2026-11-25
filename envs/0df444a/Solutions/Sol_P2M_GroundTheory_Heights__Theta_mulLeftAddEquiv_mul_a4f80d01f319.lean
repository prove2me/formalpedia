-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_mulLeftAddEquiv_mul_a4f80d01f319
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:43:21.317051+00:00
-- url     : https://prove2.me/submissions/08882ef2-4905-4a03-a0c3-e1f6b613a802

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LocallyCompactField_Countability
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_mulLeftAddEquiv_apply_ae5c0d4341c5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open MeasureTheory Measure Filter Topology Set
open scoped NNReal ENNReal Pointwise
variable {R : Type*} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    mulLeftAddEquiv (a * b) (mul_ne_zero ha hb) =
      (mulLeftAddEquiv b hb).trans (mulLeftAddEquiv a ha) := by
  ext x
  simp [mulLeftAddEquiv_apply, mul_assoc]
end GroundTheory.Heights₂.Theta
