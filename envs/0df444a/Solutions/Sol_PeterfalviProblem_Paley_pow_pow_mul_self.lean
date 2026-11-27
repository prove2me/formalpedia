-- Prove2me | solution 1 for PeterfalviProblem.Paley.pow_pow_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-27T04:59:01.836631+00:00
-- url     : https://prove2.me/submissions/8347766e-f5cc-4ef3-bf9b-d442a7432a01

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet

set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
variable {E : ℕ}
namespace PeterfalviProblem.Paley
theorem _root_.solution (hcube : ∀ z : F, z ^ (E * E * E) = z) (z : F) :
    (z ^ E) ^ (E * E) = z := by
  rw [← pow_mul, ← mul_assoc]
  exact hcube z
end PeterfalviProblem.Paley
