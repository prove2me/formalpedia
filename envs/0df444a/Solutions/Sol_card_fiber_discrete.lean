-- Prove2me | solution 1 for card_fiber_discrete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:27.937303+00:00
-- url     : https://prove2.me/submissions/fecb1f72-6dfa-416b-95ef-9b56cce49b63

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_ncard_opensOf_bot
import Theorems.Thm_ncard_minimalBasis_bot
import Theorems.Thm_card_fiber


set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem _root_.solution :
    Fintype.card (Fiber (⊥ : TopologicalSpace α)) =
      2 ^ (2 ^ Fintype.card α - Fintype.card α) := by
  rw [card_fiber, ncard_opensOf_bot, ncard_minimalBasis_bot]
