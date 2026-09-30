-- Prove2me | solution 1 for WeierstrassEllipticZeta.canonical_box_weighted_face_minimum
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T21:13:47.543312+00:00
-- url     : https://prove2.me/submissions/f9f185b3-baec-4e30-b386-152889d5be21

import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped Classical

noncomputable section

theorem solution
    (σ : Type*) [Fintype σ] [DecidableEq σ] (d t : σ → ℕ) :
    ∃ b : σ →₀ ℕ,
      (∀ i : σ, d i ≤ b i) ∧
      (∀ i : σ, t i ≤ b i + 1) ∧
      (∀ i : σ, b i + 1 = max (d i + 1) (t i)) ∧
      (∑ i : σ, d i * ∏ j ∈ (Finset.univ : Finset σ).erase i, (b j + 1)) =
        ∑ i : σ, d i * ∏ j ∈ (Finset.univ : Finset σ).erase i,
          max (d j + 1) (t j) ∧
      ∀ b' : σ →₀ ℕ,
        (∀ i : σ, d i ≤ b' i) → (∀ i : σ, t i ≤ b' i + 1) →
          (∑ i : σ, d i * ∏ j ∈ (Finset.univ : Finset σ).erase i,
            max (d j + 1) (t j)) ≤
          ∑ i : σ, d i * ∏ j ∈ (Finset.univ : Finset σ).erase i, (b' j + 1) := by
  classical
  let b : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => max (d i) (t i - 1))
  have hb (i : σ) : b i = max (d i) (t i - 1) := rfl
  have hsides (i : σ) : b i + 1 = max (d i + 1) (t i) := by
    rw [hb]
    omega
  refine ⟨b, ?_, ?_, hsides, ?_, ?_⟩
  · intro i
    rw [hb]
    exact le_max_left _ _
  · intro i
    rw [hsides]
    exact le_max_right _ _
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact Finset.prod_congr rfl (fun j _ => hsides j)
  · intro b' hdegree hcount
    apply Finset.sum_le_sum
    intro i _
    apply Nat.mul_le_mul_left
    apply Finset.prod_le_prod'
    intro j _
    exact max_le (add_le_add (hdegree j) le_rfl) (hcount j)
