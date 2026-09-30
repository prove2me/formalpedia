-- Prove2me | solution 1 for SupplyChainTheory.reduced_matrix_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T20:30:58.151778+00:00
-- url     : https://prove2.me/submissions/c4a80b8b-51e1-48d6-8ca6-9a2aa5697299

import Mathlib
import Definitions.Def_SupplyChainTheory_tsp

open Classical SupplyChainTheory

theorem solution {n : ℕ} (c : Fin n → Fin n → ℝ) (hn : 2 ≤ n) (ρ κ : Fin n → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ i j, i ≠ j → 0 ≤ reducedCost c ρ κ i j) :
    ∑ i, ρ i + ∑ j, κ j ≤ optTourLength c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Consecutive tour nodes are distinct, since `finRotate` has no fixed point for `n ≥ 2`.
  have hrot : ∀ k : Fin (m + 1), finRotate (m + 1) k ≠ k := by
    intro k h
    rw [finRotate_apply] at h
    have h1 : (1 : Fin (m + 1)) = 0 := by simpa using h
    have := congrArg Fin.val h1
    rw [Fin.val_one', Nat.one_mod_eq_one.mpr (by omega)] at this
    simp at this
  have hbound : ∀ τ : Equiv.Perm (Fin (m + 1)), ∑ i, ρ i + ∑ j, κ j ≤ tourLength c τ := by
    intro τ
    have hne : ∀ k, τ k ≠ τ (finRotate (m + 1) k) := fun k h => hrot k (τ.injective h).symm
    have hk : ∀ k, ρ (τ k) + κ (τ (finRotate (m + 1) k)) ≤ c (τ k) (τ (finRotate (m + 1) k)) := by
      intro k
      have := hc _ _ (hne k)
      simp only [reducedCost] at this
      linarith
    calc ∑ i, ρ i + ∑ j, κ j
        = ∑ k, ρ (τ k) + ∑ k, κ ((τ * finRotate (m + 1)) k) := by
          rw [Equiv.sum_comp τ ρ, Equiv.sum_comp (τ * finRotate (m + 1)) κ]
      _ = ∑ k, (ρ (τ k) + κ (τ (finRotate (m + 1) k))) := by
          rw [Finset.sum_add_distrib]; rfl
      _ ≤ tourLength c τ := Finset.sum_le_sum (fun k _ => hk k)
  exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨τ, rfl⟩; exact hbound τ)
