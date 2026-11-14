-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.uniform_cutoff_prefix_deletions_le_chain_budget
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:59:44.822197+00:00
-- url     : https://prove2.me/submissions/e990e2f3-06f7-4213-87be-01d07721f799

import Mathlib
noncomputable section
open scoped Classical BigOperators

/-- A uniformly permuted prefix is unchanged by swapping two of its positions. -/
theorem uniform_prefix_selected_position_exchange {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (i j : α) (hi : i ∈ S) (hj : j ∈ S)
    (cost : Finset α → α → ℝ) :
    (∑ π : Equiv.Perm α, cost (S.image π) (π i)) =
      ∑ π : Equiv.Perm α, cost (S.image π) (π j) := by
  classical
  let σ := Equiv.swap i j
  have hσ : S.image σ = S := by
    have hsub : S.image σ ⊆ S := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      by_cases h1 : y = i
      · subst y; simpa [σ] using hj
      · by_cases h2 : y = j
        · subst y; simpa [σ] using hi
        · simpa [σ,Equiv.swap_apply_of_ne_of_ne h1 h2] using hy
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injective S σ.injective]
  let e : Equiv.Perm (Equiv.Perm α) := Equiv.mulRight σ
  let f : Equiv.Perm α → ℝ := fun π => cost (S.image π) (π i)
  have hre := Equiv.sum_comp e f
  have hpoint (π : Equiv.Perm α) : f (e π) = cost (S.image π) (π j) := by
    dsimp [f,e]
    have himage : S.image (π ∘ σ) = S.image π := by
      rw [← Finset.image_image, hσ]
    rw [himage]
    simp [σ]
  simp_rw [hpoint] at hre
  exact hre.symm

/-- Summing deletions of all retained prefix elements equals prefix size times the last-edge sum. -/
theorem uniform_prefix_deletion_sum_eq_last_edge {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (j : α) (hj : j ∈ S) (cost : Finset α → α → ℝ) :
    (∑ π : Equiv.Perm α, ∑ i ∈ S, cost (S.image π) (π i)) =
      S.card * ∑ π : Equiv.Perm α, cost (S.image π) (π j) := by
  classical
  rw [Finset.sum_comm]
  calc
    _ = ∑ _i ∈ S, ∑ π : Equiv.Perm α, cost (S.image π) (π j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact uniform_prefix_selected_position_exchange S i j hi hj cost
    _ = _ := by simp

/-- Averaging a uniform cutoff suppresses the size of each retained-prefix deletion sum. -/
theorem solution
    {α τ : Type} [Fintype α] [DecidableEq α] [Fintype τ]
    (S : τ → Finset α) (last : τ → α) (cost : τ → Finset α → α → ℝ) (B : ℝ)
    (hsize : ∀ q, (S q).card ≤ Fintype.card τ)
    (hlast : ∀ q, S q ≠ ∅ → last q ∈ S q)
    (hnonneg : ∀ q π, 0 ≤ cost q ((S q).image π) (π (last q)))
    (hchain : ∀ π : Equiv.Perm α,
      (∑ q : τ, if S q = ∅ then 0 else cost q ((S q).image π) (π (last q))) ≤ B) :
    (∑ q : τ, ∑ π : Equiv.Perm α, ∑ i ∈ S q, cost q ((S q).image π) (π i)) ≤
      (Fintype.card τ : ℝ) * (Fintype.card (Equiv.Perm α) : ℝ) * B := by
  classical
  let d : Equiv.Perm α → τ → ℝ := fun π q => if S q = ∅ then 0 else cost q ((S q).image π) (π (last q))
  have hd (π : Equiv.Perm α) (q : τ) : 0 ≤ d π q := by
    dsimp [d]
    split <;> simp_all
  have hq (q : τ) :
      (∑ π : Equiv.Perm α, ∑ i ∈ S q, cost q ((S q).image π) (π i)) ≤
        (Fintype.card τ : ℝ) * ∑ π : Equiv.Perm α, d π q := by
    by_cases h : S q = ∅
    · simp [h,d]
    · rw [uniform_prefix_deletion_sum_eq_last_edge (S q) (last q) (hlast q h) (cost q)]
      have hsum : 0 ≤ ∑ π : Equiv.Perm α, d π q := Finset.sum_nonneg (fun π _ => hd π q)
      have hh : (S q).card * (∑ π : Equiv.Perm α, d π q) ≤
          (Fintype.card τ : ℝ) * (∑ π : Equiv.Perm α, d π q) := by
        apply mul_le_mul_of_nonneg_right _ hsum
        exact_mod_cast hsize q
      simpa [d,h] using hh
  calc
    _ ≤ ∑ q : τ, (Fintype.card τ : ℝ) * ∑ π : Equiv.Perm α, d π q := Finset.sum_le_sum (fun q _ => hq q)
    _ = (Fintype.card τ : ℝ) * ∑ π : Equiv.Perm α, ∑ q : τ, d π q := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (Fintype.card τ : ℝ) * ((Fintype.card (Equiv.Perm α) : ℝ) * B) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      simpa using Finset.sum_le_card_nsmul (Finset.univ : Finset (Equiv.Perm α)) (fun π => ∑ q : τ, d π q) B (fun π _ => hchain π)
    _ = _ := by ring
