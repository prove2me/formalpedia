-- Prove2me | solution 1 for ThreeSum.Arithmetic.exists_aux_not_dvd_of_prod_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:14:04.265682+00:00
-- url     : https://prove2.me/submissions/e6a5d57e-03af-496e-b5ba-1412e6af5fe2

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic

set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators
namespace ThreeSum.Arithmetic
theorem _root_.solution (L : Finset ℤ) (x : ℤ)
    (hcop : (L : Set ℤ).Pairwise (fun a b => IsCoprime a b))
    (hx : x ≠ 0) (hbound : x.natAbs < (∏ l ∈ L, l).natAbs) :
    ∃ l ∈ L, ¬ l ∣ x := by
  classical
  by_contra hnone
  push_neg at hnone
  have hdiv : (∏ l ∈ L, l) ∣ x := Finset.prod_dvd_of_coprime hcop hnone
  have hle := Int.natAbs_le_of_dvd_ne_zero hdiv hx
  omega
end ThreeSum.Arithmetic
