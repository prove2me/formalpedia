-- Prove2me | solution 1 for allC_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:51:30.927065+00:00
-- url     : https://prove2.me/submissions/7022e293-ef03-4509-904d-32c151a83f7f

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
theorem _root_.solution : allC (nat_lit 2) := by grind [allC, allB, allA]
