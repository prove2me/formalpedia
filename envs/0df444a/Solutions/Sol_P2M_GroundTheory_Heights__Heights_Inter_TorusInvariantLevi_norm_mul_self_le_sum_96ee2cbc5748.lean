-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_norm_mul_self_le_sum_96ee2cbc5748
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:58:36.540117+00:00
-- url     : https://prove2.me/submissions/b136e455-b9ce-46ab-b09c-29f82c0729eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
theorem _root_.solution (v : J → ℂ) : ‖v‖ * ‖v‖ ≤ ∑ p, ‖v p‖ ^ 2 := by
  have hS : 0 ≤ ∑ p, ‖v p‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h : ‖v‖ ≤ Real.sqrt (∑ p, ‖v p‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun p => ?_
    exact (le_abs_self _).trans (Real.abs_le_sqrt (Finset.single_le_sum (f := fun p => ‖v p‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ p)))
  calc ‖v‖ * ‖v‖ ≤ Real.sqrt (∑ p, ‖v p‖ ^ 2) * Real.sqrt (∑ p, ‖v p‖ ^ 2) :=
        mul_self_le_mul_self (norm_nonneg _) h
    _ = _ := Real.mul_self_sqrt hS
end GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
