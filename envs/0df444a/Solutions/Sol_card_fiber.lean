-- Prove2me | solution 1 for card_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:45:11.857136+00:00
-- url     : https://prove2.me/submissions/9c509315-7ebe-4202-a449-ad5d541e6dcb

import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.Sum
import Definitions.Def_CARDB
import Theorems.Thm_minimalBasis_subset_opens

set_option autoImplicit true
open Set TopologicalSpace
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (t : TopologicalSpace α)
omit [DecidableEq α]
theorem _root_.solution :
    Fintype.card (Fiber t) =
      2 ^ (ncard (opensOf t) - ncard (minimalBasis t)) := by
  classical
  rw [Fintype.card_congr (fiberEquiv t), Fintype.card_set]
  congr 1
  rw [← Nat.card_eq_fintype_card]
  change Nat.card ↥({U : Set α | t.IsOpen U ∧ U ∉ minimalBasis t}) = _
  rw [Nat.card_coe_set_eq,
    show {U : Set α | t.IsOpen U ∧ U ∉ minimalBasis t} = opensOf t \ minimalBasis t by
      ext U; simp [opensOf, mem_diff]]
  exact ncard_diff (minimalBasis_subset_opens t)
