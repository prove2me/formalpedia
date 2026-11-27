-- Prove2me | solution 1 for PeterfalviProblem.Paley.isSquare_or_isSquare_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-27T04:59:17.499641+00:00
-- url     : https://prove2.me/submissions/2398ae5a-e5b1-4368-94d6-f7949d8f6f85

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet

set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
namespace PeterfalviProblem.Paley
theorem _root_.solution [Fintype F] (h2 : ringChar F ≠ 2)
    (h4 : Fintype.card F % 4 = 3) {a : F} (ha : a ≠ 0) : IsSquare a ∨ IsSquare (-a) := by
  rcases FiniteField.pow_dichotomy h2 ha with h | h
  · exact Or.inl ((FiniteField.isSquare_iff h2 ha).mpr h)
  · refine Or.inr ((FiniteField.isSquare_iff h2 (neg_ne_zero.mpr ha)).mpr ?_)
    have hodd : Odd (Fintype.card F / 2) := Nat.odd_iff.mpr (by omega)
    rw [neg_pow, hodd.neg_one_pow, h]
    ring
end PeterfalviProblem.Paley
