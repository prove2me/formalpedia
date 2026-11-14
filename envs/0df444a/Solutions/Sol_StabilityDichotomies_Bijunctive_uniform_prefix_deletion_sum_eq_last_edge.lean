-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.uniform_prefix_deletion_sum_eq_last_edge
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:59:43.455206+00:00
-- url     : https://prove2.me/submissions/cee03267-45ca-4a78-bd7e-f289f196f2ea

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
theorem solution {α : Type} [Fintype α] [DecidableEq α]
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

