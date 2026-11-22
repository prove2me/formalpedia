-- Prove2me | solution 1 for chebyshev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:09.840128+00:00
-- url     : https://prove2.me/submissions/9a1ffab8-b45a-41fb-b468-650b9817c680

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_Polychromatic_DiscreteProbability
import Theorems.Thm_markov

set_option autoImplicit true
open Finset
variable {ι α : Type*} {s : Finset ι} {p f : ι → α} {c : α} [LinearOrder α]
theorem _root_.solution [DivisionRing α] [IsStrictOrderedRing α]
    (hp : ∀ i ∈ s, 0 ≤ p i) (hc : 0 < c) :
    ∑ i ∈ s with c ≤ |f i|, p i ≤ (∑ i ∈ s, p i * f i ^ 2) / c ^ 2 := by
  convert markov (f := (f · ^ 2)) hp (c := c ^ 2) (by simp [sq_nonneg]) (pow_pos hc _) using 3
  rw [sq_le_sq, abs_of_pos hc]
