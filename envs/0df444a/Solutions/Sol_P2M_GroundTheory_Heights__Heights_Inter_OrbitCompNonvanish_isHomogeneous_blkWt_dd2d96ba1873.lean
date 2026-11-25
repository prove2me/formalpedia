-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_OrbitCompNonvanish_isHomogeneous_blkWt_dd2d96ba1873
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:52.736276+00:00
-- url     : https://prove2.me/submissions/83a23896-fd34-4909-854b-7fad8d87db67

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
theorem _root_.solution {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blkWt (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := hP
  apply Ideal.homogeneous_span
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  refine ⟨Finsupp.equivFunOnFinite.symm a, (mem_weightedHomogeneousSubmodule ℤ _ _ _).mpr ?_⟩
  intro m hm
  ext k
  rw [weight_blkWt_apply, ha m (mem_support_iff.mpr hm) k]
  simp
end OrbitCompNonvanish
end GroundTheory.Heights₂.Heights.Inter
