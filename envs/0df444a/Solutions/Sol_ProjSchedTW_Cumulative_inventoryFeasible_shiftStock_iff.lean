-- Prove2me | solution 1 for ProjSchedTW.Cumulative.inventoryFeasible_shiftStock_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:45:51.474528+00:00
-- url     : https://prove2.me/submissions/2e13ed38-3186-46a5-81a4-e8c7dfa4ed86

import Mathlib
import Definitions.Def_ProjSchedTW_Cumulative_Model

open ProjSchedTW.Cumulative in
theorem dcfec505_inv_eq {n : ℕ} {K : Type} (P : CumulativeProject n K)
    (S : Fin (n + 2) → ℝ) (hS : IsSchedule S) (k : K) (t : ℝ) (ht : 0 ≤ t) :
    inventory P S k t = P.r 0 k + ∑ i : Fin (n + 1),
      (if (P.r i.succ k < 0 ∧ S i.succ ≤ t) ∨ (0 < P.r i.succ k ∧ S i.succ + (P.p i.succ : ℝ) ≤ t)
        then P.r i.succ k else 0) := by
  unfold inventory activeSet
  rw [Finset.sum_filter, Fin.sum_univ_succ]
  congr 1
  split_ifs with h
  · rfl
  · rw [hS.1, P.p_zero] at h
    simp only [Nat.cast_zero, add_zero, ht, and_true, not_or, not_lt] at h
    omega

open ProjSchedTW.Cumulative in
theorem dcfec505_inv_shift {n : ℕ} {K : Type} (P : CumulativeProject n K) (a : K → ℤ)
    (S : Fin (n + 2) → ℝ) (hS : IsSchedule S) (k : K) (t : ℝ) (ht : 0 ≤ t) :
    inventory (shiftStock P a) S k t = inventory P S k t + a k := by
  rw [dcfec505_inv_eq _ S hS k t ht, dcfec505_inv_eq P S hS k t ht]
  have h0 : (shiftStock P a).r 0 k = P.r 0 k + a k := by simp [shiftStock]
  have hs : ∀ i : Fin (n + 1), (shiftStock P a).r i.succ k = P.r i.succ k := by
    intro i; simp [shiftStock, Fin.succ_ne_zero]
  have hp : (shiftStock P a).p = P.p := rfl
  simp only [h0, hs, hp]
  ring

open ProjSchedTW.Cumulative in
theorem solution {n : ℕ} {K : Type} (P : CumulativeProject n K)
    (a : K → ℤ) (S : Fin (n + 2) → ℝ) (hS : IsSchedule S) :
    InventoryFeasible (shiftStock P a) S ↔ InventoryFeasible P S := by
  have hlo : ∀ k, (shiftStock P a).Rlow k = P.Rlow k + a k := fun k => rfl
  have hup : ∀ k, (shiftStock P a).Rup k = P.Rup k + a k := fun k => rfl
  unfold InventoryFeasible
  constructor
  · intro h k t ht
    have := h k t ht
    rw [dcfec505_inv_shift P a S hS k t ht, hlo, hup] at this
    omega
  · intro h k t ht
    have := h k t ht
    rw [dcfec505_inv_shift P a S hS k t ht, hlo, hup]
    omega
