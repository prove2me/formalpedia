-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_weight_multiDegWeight_ca852a704747
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:45.257096+00:00
-- url     : https://prove2.me/submissions/b16fc88a-6b21-4b05-9ed9-52607353c526

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_weight_blockWeight


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
namespace GroundTheory.Heights₂.Heights.Inter.LocRingPow
theorem _root_.solution (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (multiDegWeight ι) m = fun k => ∑ i, m ⟨k, i⟩ := by
  classical
  funext k
  rw [← weight_blockWeight k m, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
    Finset.sum_apply]
  simp only [Pi.smul_apply, multiDegWeight, blockWeight]
end GroundTheory.Heights₂.Heights.Inter.LocRingPow
