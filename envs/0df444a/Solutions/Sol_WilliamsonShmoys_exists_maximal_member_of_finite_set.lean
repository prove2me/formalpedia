-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_member_of_finite_set
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:33:29.434984+00:00
-- url     : https://prove2.me/submissions/c4871b0e-fbe1-40bd-8fb0-2bf4dd39abea

import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (S : Set α) (hS : S.Nonempty) :
    ∃ a, a ∈ S ∧ ∀ b, b ∈ S → a ≤ b → b ≤ a := by
  have hfin : S.Finite := Set.toFinite S
  obtain ⟨a, ha, hmax⟩ := hfin.exists_maximal hS
  refine ⟨a, ha, ?_⟩
  intro b hb hab
  exact hmax hb hab
