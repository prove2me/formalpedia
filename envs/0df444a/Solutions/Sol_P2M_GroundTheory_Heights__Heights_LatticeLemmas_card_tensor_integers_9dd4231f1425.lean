-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_tensor_integers_9dd4231f1425
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:22:53.101931+00:00
-- url     : https://prove2.me/submissions/928c8015-a732-405a-9596-17bedece9ed5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_BaseChangeIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_tensor_quotient_5d81cc5f85b5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField TensorProduct
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (Q : Type*) [AddCommGroup Q] [Module (𝓞 K) Q] [Finite Q] :
    Nat.card (𝓞 L ⊗[𝓞 K] Q) = Nat.card Q ^ Module.finrank K L := by
  induction hn : Nat.card Q using Nat.strong_induction_on generalizing Q with
  | _ n ih =>
  subst hn
  rcases subsingleton_or_nontrivial Q with hQ | hQ
  · have h0 : ∀ z : 𝓞 L ⊗[𝓞 K] Q, z = 0 := fun z ↦ by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul b q => rw [Subsingleton.elim q 0, tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    have : Subsingleton (𝓞 L ⊗[𝓞 K] Q) := ⟨fun x y ↦ by rw [h0 x, h0 y]⟩
    rw [Nat.card_of_subsingleton (0 : 𝓞 L ⊗[𝓞 K] Q), Nat.card_of_subsingleton (0 : Q), one_pow]
  obtain ⟨x, hx⟩ := exists_ne (0 : Q)
  set C : Submodule (𝓞 K) Q := Submodule.span (𝓞 K) {x}
  have : Finite (Q ⧸ C) := Finite.of_surjective _ (Submodule.mkQ_surjective C)
  have hCQ : Nat.card Q = Nat.card (Q ⧸ C) * Nat.card C :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup C.toAddSubgroup
  have hC1 : 1 < Nat.card C := by
    have : Nontrivial C := ⟨⟨⟨x, Submodule.mem_span_singleton_self x⟩, 0, fun h ↦ hx (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have hlt : Nat.card (Q ⧸ C) < Nat.card Q := by
    have : 0 < Nat.card (Q ⧸ C) := Nat.card_pos
    rw [hCQ]
    exact lt_mul_of_one_lt_right this hC1
  have hquot := ih _ hlt (Q ⧸ C) rfl
  have hcyc : Nat.card (𝓞 L ⊗[𝓞 K] C) = Nat.card C ^ Module.finrank K L := by
    have e := Ideal.quotTorsionOfEquivSpanSingleton (𝓞 K) Q x
    rw [← Nat.card_congr e.toEquiv, ← card_tensor_quotient L,
      Nat.card_congr (LinearEquiv.lTensor (𝓞 L) e).toEquiv]
  set f : 𝓞 L ⊗[𝓞 K] C →ₗ[𝓞 K] 𝓞 L ⊗[𝓞 K] Q := LinearMap.lTensor (𝓞 L) C.subtype
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap C.subtype C.injective_subtype
  have h1 : Nat.card (𝓞 L ⊗[𝓞 K] Q) =
      Nat.card ((𝓞 L ⊗[𝓞 K] Q) ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.range f).toAddSubgroup
  have h2 : Nat.card (LinearMap.range f) = Nat.card (𝓞 L ⊗[𝓞 K] C) :=
    Nat.card_congr (LinearEquiv.ofInjective f hf).toEquiv.symm
  have h3 : Nat.card ((𝓞 L ⊗[𝓞 K] Q) ⧸ LinearMap.range f) = Nat.card (𝓞 L ⊗[𝓞 K] (Q ⧸ C)) :=
    Nat.card_congr (TensorProduct.tensorQuotientEquiv (𝓞 L) C).toEquiv.symm
  rw [h1, h2, h3, hquot, hcyc, hCQ, mul_pow]
end GroundTheory.Heights₂.Heights.LatticeLemmas
