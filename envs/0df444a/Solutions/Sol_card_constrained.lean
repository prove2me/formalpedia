-- Prove2me | solution 1 for card_constrained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:49.988644+00:00
-- url     : https://prove2.me/submissions/d99b21fb-761f-43ad-96a1-8af4671cc8fa

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_card_rest
import Theorems.Thm_packConstrained_injective

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution (hne : x ≠ y) :
    ncard {U : Set α | x ∈ U → y ∈ U} ≤ 3 * 2 ^ (Fintype.card α - 2) := by
  classical
  haveI : DecidablePred (fun U : Set α => x ∈ U → y ∈ U) := fun _ => inferInstance
  haveI : Fintype {U : Set α // x ∈ U → y ∈ U} := Subtype.fintype _
  have hle := Fintype.card_le_of_injective (packConstrained x y hne)
    (packConstrained_injective x y hne)
  have hcard : ncard {U : Set α | x ∈ U → y ∈ U} =
      Fintype.card {U : Set α // x ∈ U → y ∈ U} := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hcard]
  refine hle.trans ?_
  rw [Fintype.card_prod, Fintype.card_set, Fintype.card_fin, card_rest hne, mul_comm]
