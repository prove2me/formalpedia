-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_isCompact_unitSphereDot_855e9264b529
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:19.106428+00:00
-- url     : https://prove2.me/submissions/98748b79-af1f-4fe1-8fd1-d0cb689ff9aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PImTauBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution (g : ℕ) : IsCompact (unitSphereDot g) := by
  have hc : IsClosed (unitSphereDot g) :=
    isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
  refine (isCompact_closedBall (0 : Fin g → ℝ) 1).of_isClosed_subset hc ?_
  intro u hu
  have hu' : u ⬝ᵥ u = 1 := hu
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_le_one_iff_mul_self_le_one]
  have : u i * u i ≤ u ⬝ᵥ u :=
    Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg (u j))
      (Finset.mem_univ i)
  linarith
end GroundTheory.Heights₂.Heights.Regular
