-- Prove2me | solution 1 for SubsetShrink.LowerBound.eq_39
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T01:07:50.192811+00:00
-- url     : https://prove2.me/submissions/43074cfa-3b23-4e57-a57c-826cff13977e

import Mathlib
import Definitions.Def_SubsetShrink_LowerBound_Model

namespace SSLBeq39

open SubsetShrink.LowerBound

theorem G_identity {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (βstar βt : Fin p → ℝ) (ε : Fin n → ℝ) (β : Fin p → ℝ) :
    Gfun X (X.mulVec βstar + ε) βt β =
      ∑ i, (X.mulVec β i - X.mulVec βt i) ^ 2 +
        2 * SubsetShrink.Events.dot (X.mulVec βstar - X.mulVec βt + ε) (X.mulVec βt - X.mulVec β) := by
  simp only [Gfun, SubsetShrink.Events.dot, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem decomp {p : ℕ} (βt β : Fin p → ℝ) (h : ∀ j ∈ supp βt, β j = βt j) :
    β = βt + restrict β (supp βt)ᶜ := by
  funext j
  simp only [Pi.add_apply, restrict, Finset.mem_compl]
  by_cases hj : j ∈ supp βt
  · simp [hj, h j hj]
  · have : βt j = 0 := by
      by_contra hne
      exact hj (by simp [supp, hne])
    simp [hj, this]

theorem G_eq_H {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (βstar βt : Fin p → ℝ) (ε : Fin n → ℝ) (β : Fin p → ℝ)
    (h : ∀ j ∈ supp βt, β j = βt j) :
    Gfun X (X.mulVec βstar + ε) βt β =
      Hfun X (X.mulVec βstar - X.mulVec βt + ε) (restrict β (supp βt)ᶜ) := by
  rw [G_identity]
  have hd := decomp βt β h
  set u := restrict β (supp βt)ᶜ
  have hX : X.mulVec β = X.mulVec βt + X.mulVec u := by
    conv_lhs => rw [hd]
    rw [Matrix.mulVec_add]
  rw [hX]
  simp only [Hfun, SubsetShrink.Events.dot, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem supp_add_subset {p : ℕ} (a b : Fin p → ℝ) : supp (a + b) ⊆ supp a ∪ supp b := by
  intro j hj
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply,
    Finset.mem_union] at hj ⊢
  by_contra hc
  push_neg at hc
  exact hj (by rw [hc.1, hc.2]; simp)

theorem l0_add_le {p : ℕ} (a b : Fin p → ℝ) : l0 (a + b) ≤ l0 a + l0 b := by
  unfold l0
  exact (Finset.card_le_card (supp_add_subset a b)).trans (Finset.card_union_le _ _)

theorem restrict_add {p : ℕ} (βt u : Fin p → ℝ) (hu : supp u ⊆ (supp βt)ᶜ) :
    restrict (βt + u) (supp βt)ᶜ = u := by
  funext j
  simp only [restrict, Finset.mem_compl, Pi.add_apply]
  by_cases hj : j ∈ supp βt
  · have : u j = 0 := by
      by_contra hne
      have : j ∈ supp u := by simp [supp, hne]
      exact (Finset.mem_compl.mp (hu this)) hj
    simp [hj, this]
  · have : βt j = 0 := by
      by_contra hne
      exact hj (by simp [supp, hne])
    simp [hj, this]

theorem agree_add {p : ℕ} (βt u : Fin p → ℝ) (hu : supp u ⊆ (supp βt)ᶜ) :
    ∀ j ∈ supp βt, (βt + u) j = βt j := by
  intro j hj
  have : u j = 0 := by
    by_contra hne
    have : j ∈ supp u := by simp [supp, hne]
    exact (Finset.mem_compl.mp (hu this)) hj
  simp [this]

end SSLBeq39

open SubsetShrink.LowerBound in
theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (βstar βt : Fin p → ℝ) (ε : Fin n → ℝ) (hβt : (l0 βt : ℝ) ≤ (k : ℝ) / 2) :
    (∀ β : Fin p → ℝ,
      Gfun X (X.mulVec βstar + ε) βt β =
        ∑ i, (X.mulVec β i - X.mulVec βt i) ^ 2 +
          2 * SubsetShrink.Events.dot (X.mulVec βstar - X.mulVec βt + ε) (X.mulVec βt - X.mulVec β)) ∧
    (∀ β : Fin p → ℝ, (∀ j ∈ supp βt, β j = βt j) → l0 β ≤ k →
      Gfun X (X.mulVec βstar + ε) βt β =
        Hfun X (X.mulVec βstar - X.mulVec βt + ε) (restrict β (supp βt)ᶜ)) ∧
    (∀ u : Fin p → ℝ, supp u ⊆ (supp βt)ᶜ → (l0 u : ℝ) ≤ (k : ℝ) / 2 →
      ∃ β : Fin p → ℝ, l0 β ≤ k ∧ (∀ j ∈ supp βt, β j = βt j) ∧
        Gfun X (X.mulVec βstar + ε) βt β ≤ Hfun X (X.mulVec βstar - X.mulVec βt + ε) u) := by
  refine ⟨fun β => SSLBeq39.G_identity X βstar βt ε β,
    fun β h _ => SSLBeq39.G_eq_H X βstar βt ε β h, ?_⟩
  intro u hu hu0
  refine ⟨βt + u, ?_, SSLBeq39.agree_add βt u hu, ?_⟩
  · have h1 := SSLBeq39.l0_add_le βt u
    have h2 : ((l0 βt + l0 u : ℕ) : ℝ) ≤ k := by push_cast; linarith
    exact h1.trans (by exact_mod_cast h2)
  · rw [SSLBeq39.G_eq_H X βstar βt ε _ (SSLBeq39.agree_add βt u hu),
      SSLBeq39.restrict_add βt u hu]
