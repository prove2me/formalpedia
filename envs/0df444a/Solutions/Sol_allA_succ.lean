-- Prove2me | solution 1 for allA_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:48:47.2926+00:00
-- url     : https://prove2.me/submissions/04a2d3ae-4509-409f-aa9d-9fe3119596b3

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_FourThree_Theory

set_option autoImplicit true
open Finset
theorem _root_.solution (A b c : ℕ) (h : Accept A b c ∨ A.gcd (b.gcd c) ≠ 1) (hA : allA A b c) :
    allA (A + 1) b c := by
  intro a ha0 hab haA habc hgcd
  obtain haA | rfl : a < A ∨ a = A := by grind
  · exact hA a ha0 hab haA habc hgcd
  grind
