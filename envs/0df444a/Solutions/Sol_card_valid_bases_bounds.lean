-- Prove2me | solution 1 for card_valid_bases_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:50:12.462029+00:00
-- url     : https://prove2.me/submissions/ea7bcf14-78ca-4eb3-aa2d-54eb74141dae

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_card_fiber_discrete
import Theorems.Thm_card_valid_bases_ge_discrete
import Theorems.Thm_card_topologies_le
import Theorems.Thm_card_fiber_le_of_ne_bot
import Theorems.Thm_card_valid_bases_sum_fiber


set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution (hN : 2 ≤ Fintype.card α) :
    2 ^ (2 ^ Fintype.card α - Fintype.card α) ≤ Fintype.card (ValidBasis α) ∧
    Fintype.card (ValidBasis α) ≤
      2 ^ (2 ^ Fintype.card α - Fintype.card α) +
        2 ^ (Fintype.card α * (Fintype.card α - 1) + 3 * 2 ^ (Fintype.card α - 2)) := by
  refine ⟨card_valid_bases_ge_discrete, ?_⟩
  rw [card_valid_bases_sum_fiber]
  have hsplit :
      ∑ τ : TopologicalSpace α, Fintype.card (Fiber τ) =
        Fintype.card (Fiber (⊥ : TopologicalSpace α)) +
          ∑ τ ∈ Finset.univ.filter (fun τ : TopologicalSpace α => τ ≠ ⊥),
            Fintype.card (Fiber τ) := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun τ : TopologicalSpace α => τ = ⊥)]
    simp [Finset.filter_eq']
  rw [hsplit, card_fiber_discrete]
  have hsum :
      ∑ τ ∈ Finset.univ.filter (fun τ : TopologicalSpace α => τ ≠ ⊥),
          Fintype.card (Fiber τ) ≤
        (Finset.univ.filter (fun τ : TopologicalSpace α => τ ≠ ⊥)).card *
          2 ^ (3 * 2 ^ (Fintype.card α - 2)) := by
    have hle' : ∀ τ ∈ Finset.univ.filter (fun τ : TopologicalSpace α => τ ≠ ⊥),
        Fintype.card (Fiber τ) ≤ 2 ^ (3 * 2 ^ (Fintype.card α - 2)) :=
      fun τ hτ => card_fiber_le_of_ne_bot (Finset.mem_filter.mp hτ).2
    have := Finset.sum_le_sum hle'
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hcard :
      (Finset.univ.filter (fun τ : TopologicalSpace α => τ ≠ ⊥)).card ≤
        2 ^ (Fintype.card α * (Fintype.card α - 1)) :=
    (Finset.card_filter_le _ _).trans (by simpa using card_topologies_le)
  have : (Finset.univ.filter (fun τ : TopologicalSpace α => τ ≠ ⊥)).card *
      2 ^ (3 * 2 ^ (Fintype.card α - 2)) ≤
        2 ^ (Fintype.card α * (Fintype.card α - 1) + 3 * 2 ^ (Fintype.card α - 2)) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hcard
  exact Nat.add_le_add_left (hsum.trans this) _
