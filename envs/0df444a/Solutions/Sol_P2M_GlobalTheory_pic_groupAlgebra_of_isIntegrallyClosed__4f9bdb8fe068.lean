-- Prove2me | solution 1 for P2M_GlobalTheory_pic_groupAlgebra_of_isIntegrallyClosed__4f9bdb8fe068
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:55:23.804618+00:00
-- url     : https://prove2.me/submissions/94ccb37f-c068-4d5b-ae99-c2e0fdda3230

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Theorems.Thm_GlobalTheory_exists_pic_linearEquiv_groupAlgebra_tensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct AlgebraMonoidAlgebra
open AddMonoidAlgebra CommRing
open GlobalTheory
namespace GlobalTheory
namespace pic_groupAlgebra_of_isIntegrallyClosed
theorem _root_.solution.{u, v, w} (A : Type u) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (X : Type v) [AddCommGroup X] [Module.Free ℤ X] :
    Function.Bijective (Pic.mapAlgebra A (AddMonoidAlgebra A X)) ∧
    (∀ (N : Type w) [AddCommGroup N] [Module (AddMonoidAlgebra A X) N]
      [Module.Invertible (AddMonoidAlgebra A X) N],
      ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module A M), Module.Invertible A M ∧
        Nonempty (N ≃ₗ[AddMonoidAlgebra A X] AddMonoidAlgebra A X ⊗[A] M)) ∧
    (∀ (M M' : Type w) [AddCommGroup M] [Module A M] [Module.Invertible A M] [AddCommGroup M']
      [Module A M'] [Module.Invertible A M'],
      Nonempty (AddMonoidAlgebra A X ⊗[A] M ≃ₗ[AddMonoidAlgebra A X]
        AddMonoidAlgebra A X ⊗[A] M') → Nonempty (M ≃ₗ[A] M')) := by
  refine ⟨pic_mapAlgebra_groupAlgebra_bijective A X, fun N _ _ _ => ?_,
    fun M M' _ _ _ _ _ _ ⟨e⟩ => ?_⟩
  · obtain ⟨M, hM⟩ := exists_pic_linearEquiv_groupAlgebra_tensor A (X := X) N
    exact ⟨M, inferInstance, inferInstance, inferInstance, hM⟩
  · refine Pic.mk_eq_mk_iff.mp (pic_mapAlgebra_addMonoidAlgebra_injective A X
      (Pic.mk_eq_mk_iff.mpr ⟨?_⟩))
    exact TensorProduct.AlgebraTensorModule.congr (.refl _ _) (Pic.mk.linearEquiv A M) ≪≫ₗ e ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (.refl _ _) (Pic.mk.linearEquiv A M').symm
end pic_groupAlgebra_of_isIntegrallyClosed
end GlobalTheory
