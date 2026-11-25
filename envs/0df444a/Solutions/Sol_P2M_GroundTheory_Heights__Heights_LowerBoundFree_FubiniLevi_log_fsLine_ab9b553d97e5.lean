-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_log_fsLine_ab9b553d97e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:03:52.096804+00:00
-- url     : https://prove2.me/submissions/63b30c60-4f83-4387-ae4b-abc1c8eb2705

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_sum_line_820fc4227819

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
theorem _root_.solution (z : (Σ _ : Unit, Fin 2) → ℂ) : Real.log ((fsLine 2).h z) = phi z := by
  have hfun : (fsLine 2).h z = ∏ k : Unit, Real.sqrt (∑ i : Fin 2, ‖z ⟨k, i⟩‖ ^ 2) := by
    simp only [fsLine, HermLine.ofMetrics, fsMetric, Pi.one_apply, zpow_one, EuclideanSpace.norm_eq]
  rw [hfun, Fintype.prod_unique, Real.log_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), phi,
    sqSum, sum_line]
  simp [Fin.sum_univ_two]
  ring
end GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
