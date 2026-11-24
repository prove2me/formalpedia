-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_ChartGram_re_inner_comm_a8b0e44bf3d7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:04.465852+00:00
-- url     : https://prove2.me/submissions/eb956053-2f2e-418b-8e5d-2c5b8f340e14

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
theorem _root_.solution (x z : F) : (⟪x, z⟫_ℂ).re = (⟪z, x⟫_ℂ).re := by
  rw [← inner_conj_symm x z, Complex.conj_re]
end ChartGram
end GroundTheory.Heights₂.Heights
