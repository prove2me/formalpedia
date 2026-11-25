-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_IsExpLieAlgebra_GKModule_apply___mem_6086aaa81b9a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:51:04.976119+00:00
-- url     : https://prove2.me/submissions/93845da3-9ee3-4683-942e-f924b02bf410

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CoeToRepresentationApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
attribute [local instance 100] LieRing.ofAssociativeRing
open Set Module
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G} {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace GroundTheory.Automorphic.IsExpLieAlgebra
namespace GKModule
theorem _root_.solution (M : h.GKModule K V) (Y : Subrepresentation M.rep) (k : K) {y : V}
    (hy : y ∈ Y.toSubmodule) : M.σ k y ∈ Y.toSubmodule :=
  Y.apply_mem_toSubmodule (FreeMonoid.of (Sum.inr k)) hy
end GKModule
end GroundTheory.Automorphic.IsExpLieAlgebra
