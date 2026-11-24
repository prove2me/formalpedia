-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_smul_bc982e9b6cbd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:14.054383+00:00
-- url     : https://prove2.me/submissions/01b0fb0d-3fb5-479a-8adc-8769d5e5b47b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators

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
theorem _root_.solution (U : Z.Opens) (r : Γ(Z, U)) (m : Γ(M, U)) :
    pullSectionOn g M U (r • m) = g.app U r • pullSectionOn g M U m :=
  Scheme.Modules.Hom.app_smul _ r m
end GroundTheory.Heights₂.Heights.Model
