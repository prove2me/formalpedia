-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_isLocallyNoetherian_of_locallyOfFiniteType_specZ_960f2c46d875
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:34.113799+00:00
-- url     : https://prove2.me/submissions/e98d0512-4c22-4ebb-9dda-61bb25ef1154

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsInvOpenInsideRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PInvOpenInsideRat

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
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {X : Scheme.{0}} (f : X ⟶ SpecZ)
    [LocallyOfFiniteType f] : IsLocallyNoetherian X := by
  refine ⟨fun U => ?_⟩
  have hZ : IsNoetherianRing Γ(SpecZ, ⊤) :=
    IsLocallyNoetherian.component_noetherian (X := SpecZ) ⟨⊤, isAffineOpen_top _⟩
  have e : (U : X.Opens) ≤ f ⁻¹ᵁ ⊤ := by simp
  have hφ := HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› ⟨⊤, isAffineOpen_top _⟩ U e
  let _ := (f.appLE ⊤ U.1 e).hom.toAlgebra
  have : Algebra.FiniteType Γ(SpecZ, ⊤) Γ(X, U) := hφ
  exact Algebra.FiniteType.isNoetherianRing Γ(SpecZ, ⊤) Γ(X, U)
end GroundTheory.Heights₂.Heights.Model
