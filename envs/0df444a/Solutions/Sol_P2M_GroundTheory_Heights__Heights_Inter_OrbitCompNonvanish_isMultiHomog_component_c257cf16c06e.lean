-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_OrbitCompNonvanish_isMultiHomog_component_c257cf16c06e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:53.780611+00:00
-- url     : https://prove2.me/submissions/56421706-6a88-48b1-94e0-2f36b0f75ab3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsOrbitCompNonvanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_POrbitCompNonvanish
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_weight_blkWt_apply


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
namespace OrbitCompNonvanish
theorem _root_.solution (E : MRing ι) (δ : K →₀ ℕ) :
    IsMultiHomog (weightedHomogeneousComponent (blkWt (ι := ι)) δ E) δ := by
  intro m hm k
  have h := weightedHomogeneousComponent_isWeightedHomogeneous (w := blkWt (ι := ι)) δ E
    (mem_support_iff.mp hm)
  rw [← weight_blkWt_apply, h]
end OrbitCompNonvanish
end GroundTheory.Heights₂.Heights.Inter
