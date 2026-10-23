-- Prove2me | solution 1 for SubsetShrink.LowerBound.eq_40
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T01:08:40.582351+00:00
-- url     : https://prove2.me/submissions/a4dbb778-474a-4a9c-ad25-c26eb28f318b

import Mathlib
import Definitions.Def_SubsetShrink_LowerBound_Model

namespace SSLBeq40

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

end SSLBeq40

namespace SSLBeq40
open SubsetShrink.LowerBound

theorem supp_smul_subset {p : ℕ} (c : ℝ) (v : Fin p → ℝ) : supp (c • v) ⊆ supp v := by
  intro j hj
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Pi.smul_apply,
    smul_eq_mul] at hj ⊢
  intro h0
  exact hj (by rw [h0, mul_zero])

theorem H_smul {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ) (v : Fin p → ℝ)
    (hXv : SubsetShrink.Events.l2 (X.mulVec v) = 1) :
    Hfun X w (SubsetShrink.Events.dot w (X.mulVec v) • v) =
      -(SubsetShrink.Events.dot w (X.mulVec v)) ^ 2 := by
  have hs : ∑ i, X.mulVec v i ^ 2 = 1 := by
    unfold SubsetShrink.Events.l2 at hXv
    have h0 : 0 ≤ ∑ i, X.mulVec v i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have := Real.sq_sqrt h0
    rw [hXv] at this
    linarith
  set c := SubsetShrink.Events.dot w (X.mulVec v) with hc
  simp only [Hfun, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have e1 : ∑ i, (c * X.mulVec v i) ^ 2 = c ^ 2 * ∑ i, X.mulVec v i ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro i _; ring
  have e2 : SubsetShrink.Events.dot w (fun i => c * X.mulVec v i) = c * c := by
    rw [hc]; simp only [SubsetShrink.Events.dot, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_; intro i _; ring
  rw [e1, hs]
  have : (c • X.mulVec v) = fun i => c * X.mulVec v i := by funext i; simp
  rw [this, e2]
  ring

end SSLBeq40

open SubsetShrink.LowerBound in
theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (βstar βt : Fin p → ℝ) (ε : Fin n → ℝ) (hβt : (l0 βt : ℝ) ≤ (k : ℝ) / 2)
    (v : Fin p → ℝ) (hv : supp v ⊆ (supp βt)ᶜ) (hv0 : (l0 v : ℝ) ≤ (k : ℝ) / 2)
    (hXv : SubsetShrink.Events.l2 (X.mulVec v) = 1) :
    Hfun X (X.mulVec βstar - X.mulVec βt + ε)
        (SubsetShrink.Events.dot (X.mulVec βstar - X.mulVec βt + ε) (X.mulVec v) • v) =
      -(SubsetShrink.Events.dot (X.mulVec βstar - X.mulVec βt + ε) (X.mulVec v)) ^ 2 ∧
    ∃ β : Fin p → ℝ, l0 β ≤ k ∧
      Gfun X (X.mulVec βstar + ε) βt β ≤
        -(SubsetShrink.Events.dot (X.mulVec βstar - X.mulVec βt + ε) (X.mulVec v)) ^ 2 := by
  have hH := SSLBeq40.H_smul X (X.mulVec βstar - X.mulVec βt + ε) v hXv
  refine ⟨hH, ?_⟩
  set c := SubsetShrink.Events.dot (X.mulVec βstar - X.mulVec βt + ε) (X.mulVec v)
  set u := c • v
  have hu : supp u ⊆ (supp βt)ᶜ := (SSLBeq40.supp_smul_subset c v).trans hv
  have hu0 : (l0 u : ℝ) ≤ (k : ℝ) / 2 := by
    have : l0 u ≤ l0 v := Finset.card_le_card (SSLBeq40.supp_smul_subset c v)
    have : (l0 u : ℝ) ≤ l0 v := by exact_mod_cast this
    linarith
  refine ⟨βt + u, ?_, ?_⟩
  · have h1 := SSLBeq40.l0_add_le βt u
    have h2 : ((l0 βt + l0 u : ℕ) : ℝ) ≤ k := by push_cast; linarith
    exact h1.trans (by exact_mod_cast h2)
  · rw [SSLBeq40.G_eq_H X βstar βt ε _ (SSLBeq40.agree_add βt u hu),
      SSLBeq40.restrict_add βt u hu, hH]
