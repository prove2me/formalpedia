-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_mulLeftAddEquiv_apply_ae5c0d4341c5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:53.711097+00:00
-- url     : https://prove2.me/submissions/7b1aad40-2578-4ef2-9dcc-ef4786c5c2a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LocallyCompactField_Countability

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
theorem _root_.solution (a : R) (ha : a ≠ 0) (x : R) : mulLeftAddEquiv a ha x = a * x := rfl
end GroundTheory.Heights₂.Theta
