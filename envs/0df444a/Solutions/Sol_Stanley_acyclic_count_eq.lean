-- Prove2me | solution 1 for Stanley.acyclic_count_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:16.377588+00:00
-- url     : https://prove2.me/submissions/5903c761-75be-42d8-b50a-14450d53e941

module
public import Definitions.Def_Stanley_Compatible
public import Mathlib.Tactic.Ring
public import Definitions.Def_Stanley_Reciprocity
public import Theorems.Thm_Stanley_eval_neg_one


set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
namespace Stanley
theorem _root_.solution :
    (-1 : ℤ) ^ Fintype.card V * (chromaticPolynomial G).eval (-1) =
      orientationCount G := by
  rw [eval_neg_one, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num
end Stanley
