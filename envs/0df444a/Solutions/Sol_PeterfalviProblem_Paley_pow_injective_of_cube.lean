-- Prove2me | solution 1 for PeterfalviProblem.Paley.pow_injective_of_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-27T05:02:39.652085+00:00
-- url     : https://prove2.me/submissions/e192cd51-ef5b-443f-8c71-144920f26995

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
import Theorems.Thm_PeterfalviProblem_Paley_pow_pow_mul_self

set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
variable {E : ℕ}
namespace PeterfalviProblem.Paley
theorem _root_.solution (hcube : ∀ z : F, z ^ (E * E * E) = z) {x y : F}
    (h : x ^ E = y ^ E) : x = y := by
  have := congrArg (· ^ (E * E)) h
  simpa only [pow_pow_mul_self hcube] using this
end PeterfalviProblem.Paley
