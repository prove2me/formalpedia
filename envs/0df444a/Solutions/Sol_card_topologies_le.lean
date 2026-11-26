-- Prove2me | solution 1 for card_topologies_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:57.560736+00:00
-- url     : https://prove2.me/submissions/7de16e64-68a7-41ff-9aba-a394ac8c0a7d

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_specOffDiag_injective
import Theorems.Thm_card_off_diag

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution :
    Fintype.card (TopologicalSpace α) ≤
      2 ^ (Fintype.card α * (Fintype.card α - 1)) := by
  have h := Fintype.card_le_of_injective
    (specOffDiag : TopologicalSpace α → Set {p : α × α // p.1 ≠ p.2})
    specOffDiag_injective
  rwa [Fintype.card_set, card_off_diag] at h
