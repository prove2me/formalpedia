-- Prove2me | solution 1 for allC_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:51:25.137419+00:00
-- url     : https://prove2.me/submissions/a5c5df6c-d1bc-4f29-8655-d377804de6e0

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
theorem _root_.solution : allC (nat_lit 1) := by grind [allC, allB]
