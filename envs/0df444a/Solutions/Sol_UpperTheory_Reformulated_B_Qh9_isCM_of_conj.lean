-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qh9.isCM_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:34:02.557679+00:00
-- url     : https://prove2.me/submissions/3a057ca5-3d8d-49ce-9e9f-eaf4565b06da

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsCMOfConjAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace UpperTheory.Reformulated.B.Qh9
theorem _root_.solution :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
    [NumberField.IsTotallyComplex K],
    (∀ (x : K), ∃ (y : K), ∀ (φ : K →+* ℂ), (φ : K → ℂ) y = (starRingEnd ℂ : ℂ → ℂ) ((φ : K → ℂ) x)) →
      NumberField.IsCMField K := by
  intro K _ _ _ h
  choose c hc using h
  let φ₀ : K →+* ℂ := Classical.choice inferInstance
  have hfix : ∀ x : K, c x = x ↔ x ∈ maximalRealSubfield K := by
    intro x
    rw [mem_maximalRealSubfield_iff]
    constructor
    · intro hx φ
      have := hc x φ
      rw [hx] at this
      exact this.symm
    · intro hx
      apply φ₀.injective
      rw [hc]
      exact hx φ₀
  have hinv : ∀ x : K, c (c x) = x := by
    intro x
    apply φ₀.injective
    simp [hc]
  let σ : K ≃ₐ[maximalRealSubfield K] K :=
    { toFun := c
      invFun := c
      left_inv := hinv
      right_inv := hinv
      map_mul' := fun x y => φ₀.injective (by simp [hc])
      map_add' := fun x y => φ₀.injective (by simp [hc])
      commutes' := fun x => (hfix _).mpr x.2 }
  have hσ : ∀ x, σ x = c x := fun _ => rfl
  have hne : σ ≠ 1 := by
    intro h1
    apply IsTotallyComplex.complexEmbedding_not_isReal φ₀
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : c x = x := by rw [← hσ, h1]; rfl
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc, hx]
  have hord : orderOf σ = 2 :=
    orderOf_eq_prime (by ext x; simp [pow_two, hσ, hinv]) hne
  have hbot : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact IntermediateField.mem_bot.mpr
      ⟨⟨x, (hfix x).mp (hx σ (Subgroup.mem_zpowers σ))⟩, rfl⟩
  have hrank := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
  rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers, hord] at hrank
  have : Algebra.IsQuadraticExtension (maximalRealSubfield K) K := ⟨hrank⟩
  exact ⟨⟩
end UpperTheory.Reformulated.B.Qh9
