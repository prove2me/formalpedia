-- Prove2me | solution 1 for PeterfalviProblem.Paley.not_isSquare_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-27T04:59:23.208464+00:00
-- url     : https://prove2.me/submissions/7b361896-fc4d-4b6a-bef5-84261a35801c

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet

set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
namespace PeterfalviProblem.Paley
theorem _root_.solution [Fintype F] (h2 : ringChar F ≠ 2) (h4 : Fintype.card F % 4 = 3) :
    ¬ IsSquare (-1 : F) := by
  have hne : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rw [FiniteField.isSquare_iff h2 hne]
  have hodd : Odd (Fintype.card F / 2) := Nat.odd_iff.mpr (by omega)
  rw [hodd.neg_one_pow]
  intro h
  have h20 : (2 : F) = 0 := by linear_combination -h
  have hdvd : ringChar F ∣ 2 := ringChar.dvd (by exact_mod_cast h20)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact h2 h1
end PeterfalviProblem.Paley
