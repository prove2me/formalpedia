-- Prove2me | solution 1 for TenChallenges.sidorenko_sum
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:36:01.066555+00:00
-- url     : https://prove2.me/submissions/67f6be35-3bed-41c7-a059-690b51bd5850

import Definitions.Def_TenChallenges_Challenge_04
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Algebra.Order.Field.Basic

/-!
# Sidorenko inequalities and disjoint unions

Homomorphism densities multiply over disjoint unions of source graphs.
Consequently Sidorenko inequalities combine across components, and adding
isolated vertices preserves both the density and the inequality.
-/

open SimpleGraph

namespace TenChallengesContinuation

variable {W₁ W₂ V : Type*} [Fintype W₁] [Fintype W₂] [Fintype V]

omit [Fintype W₁] [Fintype W₂] [Fintype V] in
/-- Restricting a homomorphism to the two components gives independent choices. -/
theorem homCount_sum (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (G : SimpleGraph V) :
    Nat.card {f : W₁ ⊕ W₂ → V // ∀ ⦃a b⦄, (H₁ ⊕g H₂).Adj a b → G.Adj (f a) (f b)} =
      Nat.card {f : W₁ → V // ∀ ⦃a b⦄, H₁.Adj a b → G.Adj (f a) (f b)} *
      Nat.card {f : W₂ → V // ∀ ⦃a b⦄, H₂.Adj a b → G.Adj (f a) (f b)} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr {
    toFun := fun f =>
      (⟨fun a => f.1 (.inl a), fun {_ _} h => f.2 h⟩,
       ⟨fun a => f.1 (.inr a), fun {_ _} h => f.2 h⟩)
    invFun := fun f =>
      ⟨Sum.elim f.1.1 f.2.1,
       fun {a b} h => match a, b, h with
       | .inl _, .inl _, h => f.1.2 h
       | .inr _, .inr _, h => f.2.2 h
       | .inl a, .inr b, h => (not_adj_sum_inl_inr a b h).elim
       | .inr b, .inl a, h => (not_adj_sum_inl_inr a b h.symm).elim⟩
    left_inv := fun f => Subtype.ext (funext fun a => match a with
      | .inl _ => rfl
      | .inr _ => rfl)
    right_inv := fun f => Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  }

/-- Homomorphism densities multiply under disjoint union of the sources. -/
theorem homDensity_sum (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (G : SimpleGraph V) :
    homDensity (H₁ ⊕g H₂) G = homDensity H₁ G * homDensity H₂ G := by
  unfold homDensity
  rw [homCount_sum, Fintype.card_sum, Nat.cast_mul, pow_add, mul_div_mul_comm]

/-- Every homomorphism density is nonnegative, including for empty target graphs. -/
theorem homDensity_nonneg (H : SimpleGraph W₁) (G : SimpleGraph V) :
    0 ≤ homDensity H G := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

omit [Fintype W₁] [Fintype W₂] in
/-- The edges of a disjoint union are the disjoint sum of the component edges. -/
theorem edgeCount_sum [Finite W₁] [Finite W₂] (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) :
    Nat.card (H₁ ⊕g H₂).edgeSet = Nat.card H₁.edgeSet + Nat.card H₂.edgeSet := by
  rw [Nat.card_congr (edgeSetSumEquiv (G := H₁) (H := H₂)), Nat.card_sum]

/-- Sidorenko inequalities for two sources imply the inequality for their disjoint union. -/
theorem sidorenko_sum (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (G : SimpleGraph V) (h₁ : SidorenkoFor H₁ G) (h₂ : SidorenkoFor H₂ G) :
    SidorenkoFor (H₁ ⊕g H₂) G := by
  unfold SidorenkoFor at h₁ h₂ ⊢
  rw [homDensity_sum, edgeCount_sum, pow_add]
  exact mul_le_mul h₁ h₂ (pow_nonneg (homDensity_nonneg _ _) _) (homDensity_nonneg _ _)

/-- An edgeless source has density one when the target is nonempty. -/
theorem homDensity_bot [Nonempty V] (G : SimpleGraph V) :
    homDensity (⊥ : SimpleGraph W₁) G = 1 := by
  classical
  unfold homDensity
  simp only [bot_adj, false_implies, implies_true, Nat.card_subtype_true]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Nat.cast_pow]
  exact div_self (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

/-- Every edgeless source satisfies Sidorenko against a nonempty target. -/
theorem sidorenko_bot [Nonempty V] (G : SimpleGraph V) :
    SidorenkoFor (⊥ : SimpleGraph W₁) G := by
  simp [SidorenkoFor, homDensity_bot, edgeSet_bot]

/-- Adding any finite set of isolated source vertices leaves the density unchanged. -/
theorem homDensity_add_isolates [Nonempty V] (H : SimpleGraph W₁)
    (G : SimpleGraph V) :
    homDensity (H ⊕g (⊥ : SimpleGraph W₂)) G = homDensity H G := by
  rw [homDensity_sum, homDensity_bot, mul_one]

/-- Isolated source vertices do not affect Sidorenko inequalities. -/
theorem sidorenko_add_isolates_iff [Nonempty V] (H : SimpleGraph W₁)
    (G : SimpleGraph V) :
    SidorenkoFor (H ⊕g (⊥ : SimpleGraph W₂)) G ↔ SidorenkoFor H G := by
  simp only [SidorenkoFor, homDensity_add_isolates, edgeCount_sum, edgeSet_bot,
    Nat.card_of_isEmpty, add_zero]

end TenChallengesContinuation

#print axioms TenChallengesContinuation.sidorenko_sum
#print axioms TenChallengesContinuation.sidorenko_add_isolates_iff


theorem solution {W₁ W₂ V : Type*} [Fintype W₁] [Fintype W₂] [Fintype V]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) (G : SimpleGraph V)
    (h₁ : SidorenkoFor H₁ G) (h₂ : SidorenkoFor H₂ G) :
    SidorenkoFor (H₁ ⊕g H₂) G :=
  TenChallengesContinuation.sidorenko_sum H₁ H₂ G h₁ h₂

#print axioms solution
