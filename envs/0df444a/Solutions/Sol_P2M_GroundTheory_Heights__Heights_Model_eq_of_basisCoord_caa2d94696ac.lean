-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_eq_of_basisCoord_caa2d94696ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:11.118806+00:00
-- url     : https://prove2.me/submissions/880e3222-c4cf-4fee-96e4-24f99e4c8f38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullbackFaithful
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PPullbackFaithful

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
variable {X : Scheme.{u}} {B : X.Modules} {n : ℕ} {s : Fin n → Γ(B, ⊤)}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (hs : IsBasisOn B ⊤ s) {A : X.Modules} (ψ₁ ψ₂ : A ⟶ B)
    (h : ∀ j, ψ₁ ≫ basisCoord hs j = ψ₂ ≫ basisCoord hs j) : ψ₁ = ψ₂ := by
  ext W x
  apply (basisEquiv hs W).symm.injective
  funext j
  exact congr((($(h j)).app W).hom x)
end GroundTheory.Heights₂.Heights.Model
