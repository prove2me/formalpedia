-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartGram_re_inner_self_pos_4ec83ff2d5a3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:50:59.626257+00:00
-- url     : https://prove2.me/submissions/9927893d-d003-40ca-a42f-2afa98675f87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped InnerProductSpace
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
namespace GroundTheory.Heights₂.Heights
namespace ChartGram
theorem _root_.solution {x : F} (h0 : x ≠ 0) : 0 < (⟪x, x⟫_ℂ).re := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) x
  have h' : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := h
  rw [h']; positivity
end ChartGram
end GroundTheory.Heights₂.Heights
