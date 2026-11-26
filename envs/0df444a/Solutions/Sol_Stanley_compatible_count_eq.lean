-- Prove2me | solution 1 for Stanley.compatible_count_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:04.755538+00:00
-- url     : https://prove2.me/submissions/c283f259-594a-423e-a002-a43f4da7d151

module
public import Definitions.Def_Stanley_Compatible
public import Mathlib.Tactic.Ring
public import Definitions.Def_Stanley_Reciprocity
public import Theorems.Thm_Stanley_reciprocity

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
namespace Stanley
theorem _root_.solution (k : ℕ) :
    (-1 : ℤ) ^ Fintype.card V * (chromaticPolynomial G).eval (-(k : ℤ)) =
      compatibleCount G k := by
  rw [reciprocity, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num
end Stanley
