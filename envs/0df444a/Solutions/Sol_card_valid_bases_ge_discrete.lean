-- Prove2me | solution 1 for card_valid_bases_ge_discrete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:49:03.83457+00:00
-- url     : https://prove2.me/submissions/26cb1fa2-d4e3-42ae-a9c4-22acf1347abb

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_card_fiber_discrete
import Theorems.Thm_card_valid_bases_sum_fiber


set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem _root_.solution :
    2 ^ (2 ^ Fintype.card α - Fintype.card α) ≤ Fintype.card (ValidBasis α) := by
  rw [card_valid_bases_sum_fiber, ← card_fiber_discrete]
  exact Finset.single_le_sum (f := fun τ : TopologicalSpace α => Fintype.card (Fiber τ))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⊥ : TopologicalSpace α))
