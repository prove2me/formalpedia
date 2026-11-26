-- Prove2me | solution 1 for card_fiber_le_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:49:27.665086+00:00
-- url     : https://prove2.me/submissions/e33c7b02-5652-4763-ba6e-a885bc3b4a2b

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_ncard_opensOf_le_of_ne_bot
import Theorems.Thm_card_fiber


set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution {t : TopologicalSpace α} (ht : t ≠ ⊥) :
    Fintype.card (Fiber t) ≤ 2 ^ (3 * 2 ^ (Fintype.card α - 2)) := by
  rw [card_fiber]
  exact Nat.pow_le_pow_right (by decide : 0 < 2)
    ((Nat.sub_le _ _).trans (ncard_opensOf_le_of_ne_bot ht))
