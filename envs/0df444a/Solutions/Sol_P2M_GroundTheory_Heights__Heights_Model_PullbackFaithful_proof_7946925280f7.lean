-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_PullbackFaithful_proof_7946925280f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:04:49.32189+00:00
-- url     : https://prove2.me/submissions/d530f1ba-4788-4b21-b955-638e8c68544b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullbackFaithful
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PPullbackFaithful
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_restrict_map_eq_of_pullback_52248e31ec6e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_app_map_apply_e9534398254a


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
namespace PullbackFaithful
theorem _root_.solution : PullbackFaithful.Statement := by
  intro T U g hg A B hB ψ₁ ψ₂ h
  choose V hVa hxV n s hs using hB
  have loc : ∀ x : U, (Scheme.Modules.restrictFunctor (V x).ι).map ψ₁ =
      (Scheme.Modules.restrictFunctor (V x).ι).map ψ₂ :=
    fun x => restrict_map_eq_of_pullback g hg (V x) (hs x) ψ₁ ψ₂ h
  ext W a
  let F : TopCat.Sheaf Ab U := ⟨B.presheaf, B.isSheaf⟩
  refine F.eq_of_locally_eq' (fun x : W => (V x).ι ''ᵁ ((V x).ι ⁻¹ᵁ W)) W
    (fun x => homOfLE ((V x.1).ι.image_preimage_le W)) ?_ _ _ fun x => ?_
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, ⟨y, hxV y⟩, hy, rfl⟩
  · change (B.presheaf.map _).hom ((ψ₁.app W).hom a) = (B.presheaf.map _).hom ((ψ₂.app W).hom a)
    rw [← app_map_apply, ← app_map_apply]
    exact congr((($(loc x.1)).app ((V x.1).ι ⁻¹ᵁ W)).hom _)
end PullbackFaithful
end GroundTheory.Heights₂.Heights.Model
