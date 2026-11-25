-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mul_of_not_le_458ee4a08c44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:48.295798+00:00
-- url     : https://prove2.me/submissions/e7f498c0-6e6c-4f30-a70d-a96108dc1182

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter.AvoidRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.LocRingPow
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.LocRingPow
theorem _root_.solution [DecidableEq K] {f g : MRing ι} {j n : K → ℕ}
    (hg : IsWeightedHomogeneous (multiDegWeight ι) g j) (h : ¬ j ≤ n) :
    weightedHomogeneousComponent (multiDegWeight ι) n (f * g) = 0 := by
  rw [← weightedDecomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_right_mem_of_not_le (weightedHomogeneousSubmodule ℤ (multiDegWeight ι))
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg) h
end GroundTheory.Heights₂.Heights.Inter.LocRingPow
