-- Prove2me | solution 1 for allA_succ_of_accept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:52:30.485379+00:00
-- url     : https://prove2.me/submissions/a71c800d-b71a-4640-ae3d-907f7e2df309

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_FourThree_Theory
import Theorems.Thm_allA_succ

set_option autoImplicit true
open Finset
theorem _root_.solution (A b c : ℕ)
    (h : Accept A b c) (hA : allA A b c) :
    allA A.succ b c := allA_succ A b c (Or.inl h) hA
