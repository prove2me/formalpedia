-- Prove2me | solution 1 for allB_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:52:14.683244+00:00
-- url     : https://prove2.me/submissions/9a4012f6-4f6f-4007-8628-eaf572254624

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
theorem _root_.solution (B c : ℕ) (ha : allA B B c) (hB : allB B c) :
    allB B.succ c := by
  intro b hbB hbc
  obtain hbB | rfl : b < B ∨ b = B := by grind
  · exact hB _ hbB hbc
  · exact ha
