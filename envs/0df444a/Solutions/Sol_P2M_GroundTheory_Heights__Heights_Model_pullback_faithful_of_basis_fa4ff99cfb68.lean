-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullback_faithful_of_basis_fa4ff99cfb68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:42:18.794404+00:00
-- url     : https://prove2.me/submissions/ebcc184a-e34b-41ca-9bf4-469341859346

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullbackFaithful
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PPullbackFaithful
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullback_map_injective_unit_98af568d62d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_eq_of_basisCoord_caa2d94696ac

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
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {T U : Scheme.{u}} (g : T ⟶ U)
    (hg : ∀ W : U.Opens, Function.Injective (g.app W)) {A B : U.Modules} {n : ℕ}
    {s : Fin n → Γ(B, ⊤)} (hs : IsBasisOn B ⊤ s) (ψ₁ ψ₂ : A ⟶ B)
    (h : (Scheme.Modules.pullback g).map ψ₁ = (Scheme.Modules.pullback g).map ψ₂) : ψ₁ = ψ₂ :=
  eq_of_basisCoord hs ψ₁ ψ₂ fun j => pullback_map_injective_unit g hg _ _
    (by rw [Functor.map_comp, Functor.map_comp, h])
end GroundTheory.Heights₂.Heights.Model
