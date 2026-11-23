-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:26.839387+00:00
-- url     : https://prove2.me/submissions/ee4f611e-3105-42e6-9f08-7ce99370be45

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_LieAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
attribute [local instance 100] LieRing.ofAssociativeRing
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (X : h.lieSubalgebra) :
    h.uAction π (UniversalEnvelopingAlgebra.ι ℝ X) = h.derivEnd π (h.ofLie X) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℝ (h.derivLie π) X
end GroundTheory.Automorphic.IsExpLieAlgebra
