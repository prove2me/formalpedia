-- Prove2me | solution 1 for allB_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:52:07.065355+00:00
-- url     : https://prove2.me/submissions/2b2b0c10-9f8d-4b40-b039-0f3a22b5c380

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
theorem _root_.solution (c : ℕ) : allB (nat_lit 1) c := by grind [allB, allA]
