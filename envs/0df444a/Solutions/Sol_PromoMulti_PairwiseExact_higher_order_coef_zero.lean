-- Prove2me | solution 1 for PromoMulti.PairwiseExact.higher_order_coef_zero
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:27:05.704268+00:00
-- url     : https://prove2.me/submissions/08c79973-7434-4d92-86d5-48a6e2ae2567

import Mathlib
import Definitions.Def_PromoMulti_PairwiseExact_Model

namespace PromoMulti.PairwiseExact
namespace SolAux

/-- Alternating sum over subsets vanishes when the summand ignores some element of `S`. -/
theorem altsum_zero {ι : Type*} [DecidableEq ι] (S A : Finset ι) (F : Finset ι → ℝ)
    (hF : ∀ U, F U = F (U ∩ A)) (hs : A.card < S.card) :
    ∑ U ∈ S.powerset, (-1 : ℝ) ^ (S.card - U.card) * F U = 0 := by
  obtain ⟨s, hsS, hsA⟩ := Finset.exists_mem_notMem_of_card_lt_card hs
  have hS : S = insert s (S.erase s) := (Finset.insert_erase hsS).symm
  set S' := S.erase s with hS'
  have hnot : s ∉ S' := Finset.notMem_erase s S
  have hcard : S.card = S'.card + 1 := by rw [hS, Finset.card_insert_of_notMem hnot]
  rw [hcard, hS, Finset.sum_powerset_insert hnot, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro U hU
  have hUS : U ⊆ S' := Finset.mem_powerset.mp hU
  have hsU : s ∉ U := fun h => hnot (hUS h)
  have hle : U.card ≤ S'.card := Finset.card_le_card hUS
  rw [Finset.card_insert_of_notMem hsU]
  have hFi : F (insert s U) = F U := by
    rw [hF (insert s U), hF U, Finset.insert_inter_of_notMem hsA]
  rw [hFi, show S'.card + 1 - U.card = (S'.card - U.card) + 1 by omega,
    show S'.card + 1 - (U.card + 1) = S'.card - U.card by omega, pow_succ]
  ring

variable {N T : ℕ}

theorem coef_eq_sum_contrib (I : Instance N T) (t : Fin T) (σ : Pattern I) :
    coef I t σ = ∑ i, ∑ τ, contrib I t σ i τ := by
  unfold coef contrib MPOP
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]

theorem pure_restrict_inter (I : Instance N T) (t : Fin T) (σ : Pattern I)
    (U A : Finset (Fin N)) (k : Fin N) (hk : k ∈ A ∨ k ∉ supp σ) :
    pure I t (restrict σ U) k = pure I t (restrict σ (U ∩ A)) k := by
  funext τ
  unfold pure restrict
  rcases hk with hk | hk
  · simp [Finset.mem_inter, hk]
  · have : σ k = 0 := by simpa [supp] using hk
    by_cases h1 : k ∈ U <;> by_cases h2 : k ∈ A <;> simp [h1, h2, this]

theorem pure_off (I : Instance N T) (t : Fin T) (σ : Pattern I)
    (U V : Finset (Fin N)) (k : Fin N) (τ : Fin T) (hτ : τ ≠ t) :
    pure I t (restrict σ U) k τ = pure I t (restrict σ V) k τ := by
  simp [pure, hτ]

theorem window_congr (I : Instance N T) (γ γ' : Plan I) (i : Fin N) (τ : Fin T)
    (hγ : γ i = γ' i) : window I γ i τ = window I γ' i τ := by
  unfold window price; rw [hγ]

theorem price_congr (I : Instance N T) (γ γ' : Plan I) (i : Fin N) (τ : Fin T)
    (hγ : γ i = γ' i) : price I γ i τ = price I γ' i τ := by
  unfold price; rw [hγ]

/-- General vanishing criterion for a contribution. -/
theorem contrib_zero_of (I : Instance N T)
    (h : (i : Fin N) → Fin T → (Fin (I.M i + 1) → ℝ) → ℝ) (H : Fin N → Fin N → Fin T → ℝ → ℝ)
    (hsep : AdditiveCross I h H) (t : Fin T) (σ : Pattern I) (i : Fin N) (τ : Fin T)
    (A : Finset (Fin N)) (B : Fin N → Finset (Fin N))
    (hA : A.card < (supp σ).card) (hB : ∀ j, (B j).card < (supp σ).card)
    (hX : ∀ U, (price I (pure I t (restrict σ U)) i τ - I.c i τ) *
        h i τ (window I (pure I t (restrict σ U)) i τ) =
      (price I (pure I t (restrict σ (U ∩ A))) i τ - I.c i τ) *
        h i τ (window I (pure I t (restrict σ (U ∩ A))) i τ))
    (hY : ∀ j U, (price I (pure I t (restrict σ U)) i τ - I.c i τ) *
        H j i τ (price I (pure I t (restrict σ U)) j τ) =
      (price I (pure I t (restrict σ (U ∩ B j))) i τ - I.c i τ) *
        H j i τ (price I (pure I t (restrict σ (U ∩ B j))) j τ)) :
    contrib I t σ i τ = 0 := by
  unfold contrib
  have hp : ∀ U, profit I (pure I t (restrict σ U)) i τ =
      (price I (pure I t (restrict σ U)) i τ - I.c i τ) *
        h i τ (window I (pure I t (restrict σ U)) i τ) +
      ∑ j ∈ Finset.univ.erase i, (price I (pure I t (restrict σ U)) i τ - I.c i τ) *
        H j i τ (price I (pure I t (restrict σ U)) j τ) := by
    intro U
    rw [profit, hsep, mul_add, Finset.mul_sum]
  simp only [hp, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  rw [altsum_zero (supp σ) A _ hX hA, zero_add]
  apply Finset.sum_eq_zero
  intro j _
  exact altsum_zero (supp σ) (B j) _ (hY j) (hB j)

theorem contrib_zero_three (I : Instance N T)
    (h : (i : Fin N) → Fin T → (Fin (I.M i + 1) → ℝ) → ℝ) (H : Fin N → Fin N → Fin T → ℝ → ℝ)
    (hsep : AdditiveCross I h H) (t : Fin T) (σ : Pattern I) (h3 : 3 ≤ (supp σ).card)
    (i : Fin N) (τ : Fin T) : contrib I t σ i τ = 0 := by
  refine contrib_zero_of I h H hsep t σ i τ {i} (fun j => {i, j}) ?_ ?_ ?_ ?_
  · simp; omega
  · intro j
    have := Finset.card_le_two (a := i) (b := j)
    omega
  · intro U
    have e := pure_restrict_inter I t σ U {i} i (Or.inl (Finset.mem_singleton_self i))
    rw [price_congr _ _ _ _ _ e, window_congr _ _ _ _ _ e]
  · intro j U
    rw [price_congr _ _ _ i _ (pure_restrict_inter I t σ U {i, j} i (Or.inl (by simp))),
      price_congr _ _ _ j _ (pure_restrict_inter I t σ U {i, j} j (Or.inl (by simp)))]

theorem higher_order_coef_zero' (I : Instance N T)
    (h : (i : Fin N) → Fin T → (Fin (I.M i + 1) → ℝ) → ℝ) (H : Fin N → Fin N → Fin T → ℝ → ℝ)
    (hsep : AdditiveCross I h H) (t : Fin T) (σ : Pattern I) (h3 : 3 ≤ (supp σ).card) :
    coef I t σ = 0 := by
  rw [coef_eq_sum_contrib]
  exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun τ _ =>
    contrib_zero_three I h H hsep t σ h3 i τ

end SolAux
end PromoMulti.PairwiseExact

open PromoMulti.PairwiseExact

theorem solution {N T : ℕ} (I : Instance N T)
    (h : (i : Fin N) → Fin T → (Fin (I.M i + 1) → ℝ) → ℝ) (H : Fin N → Fin N → Fin T → ℝ → ℝ)
    (hsep : AdditiveCross I h H) (t : Fin T) (σ : Pattern I) (h3 : 3 ≤ (supp σ).card) :
    coef I t σ = 0 :=
  SolAux.higher_order_coef_zero' I h H hsep t σ h3
