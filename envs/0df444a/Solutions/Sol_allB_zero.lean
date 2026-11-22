-- Prove2me | solution 1 for allB_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:51:45.865646+00:00
-- url     : https://prove2.me/submissions/8d09dcef-8d18-4677-99ca-47f389ea8a7c

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
theorem _root_.solution (c : ℕ) : allB (nat_lit 0) c := by grind [allB]
