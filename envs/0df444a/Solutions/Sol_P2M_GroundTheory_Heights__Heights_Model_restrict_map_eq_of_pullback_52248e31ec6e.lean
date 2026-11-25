-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_restrict_map_eq_of_pullback_52248e31ec6e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:30.653948+00:00
-- url     : https://prove2.me/submissions/67840f30-bb20-4d79-b7ea-7ede1b916ea2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullbackFaithful
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PPullbackFaithful
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullback_faithful_of_basis_fa4ff99cfb68
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_restrictImage_c6b16aec65a8


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
set_option backward.isDefEq.respectTransparency.types false
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {T U : Scheme.{u}} (g : T ⟶ U)
    (hg : ∀ W : U.Opens, Function.Injective (g.app W)) {A B : U.Modules} (V : U.Opens) {n : ℕ}
    {s : Fin n → Γ(B, V)} (hs : IsBasisOn B V s) (ψ₁ ψ₂ : A ⟶ B)
    (h : (Scheme.Modules.pullback g).map ψ₁ = (Scheme.Modules.pullback g).map ψ₂) :
    (Scheme.Modules.restrictFunctor V.ι).map ψ₁ = (Scheme.Modules.restrictFunctor V.ι).map ψ₂ := by
  have hs' := (hs.restrict V.ι_image_top.le).restrictImage V.ι
  have hg' : ∀ W, Function.Injective ((g ∣_ V).app W) := by
    intro W
    rw [morphismRestrict_app]
    exact (ConcreteCategory.bijective_of_isIso
      (T.presheaf.map (eqToHom (image_morphismRestrict_preimage g V W)).op)).1.comp (hg _)
  let E : Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pullback (g ∣_ V) ≅
      Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback (g ⁻¹ᵁ V).ι :=
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback V.ι) _ ≪≫
      Scheme.Modules.pullbackComp _ _ ≪≫
        Scheme.Modules.pullbackCongr (morphismRestrict_ι g V) ≪≫
          (Scheme.Modules.pullbackComp _ _).symm
  apply pullback_faithful_of_basis (g ∣_ V) hg' hs'
  refine (NatIso.naturality_2 E ψ₁).symm.trans (Eq.trans ?_ (NatIso.naturality_2 E ψ₂))
  simp only [Functor.comp_map, h]
end GroundTheory.Heights₂.Heights.Model
