-- Prove2me | solution 1 for allC_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:51:41.504579+00:00
-- url     : https://prove2.me/submissions/58e29165-ead8-48dc-800d-18b09bc1845e

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
theorem _root_.solution (C : ℕ) (hb : allB C C) (hC : allC C) : allC C.succ := by
  intro c hc
  obtain hc | rfl : c < C ∨ c = C := by grind
  · exact hC c hc
  · exact hb
