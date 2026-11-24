-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_sum_a72fcb193ca9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:54:40.745785+00:00
-- url     : https://prove2.me/submissions/692a812f-d0ef-457c-a912-53f2e5d779bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_smul_bc982e9b6cbd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {T Z : Scheme.{0}} (g : T ⟶ Z) (M : Z.Modules)
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (U : Z.Opens) {n : ℕ} (t : Fin n → Γ(M, U)) (r : Fin n → Γ(Z, U)) :
    pullSectionOn g M U (∑ i, r i • t i) = ∑ i, g.app U (r i) • pullSectionOn g M U (t i) := by
  rw [map_sum]
  simp only [pullSectionOn_smul]
end GroundTheory.Heights₂.Heights.Model
