-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_isVectorBundle_structureModule_93a0cef3461d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:55.971914+00:00
-- url     : https://prove2.me/submissions/883171fe-eebf-4cae-bdd1-fee4dd6157b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements

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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
variable {X : Scheme.{u}}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution : IsVectorBundle (structureModule X) := by
  intro x
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ (⊤ : X.Opens) from trivial)
  refine ⟨U, hU, hxU, 1, fun _ => (1 : Γ(X, U)), ?_⟩
  intro V h
  change Function.Bijective (fun r : Fin 1 → Γ(X, V) =>
    ∑ i, r i * (X.presheaf.map (homOfLE h).op).hom 1)
  simp only [map_one, mul_one, Fin.sum_univ_one]
  exact (Equiv.funUnique (Fin 1) Γ(X, V)).bijective
end GroundTheory.Heights₂.Heights.Model
