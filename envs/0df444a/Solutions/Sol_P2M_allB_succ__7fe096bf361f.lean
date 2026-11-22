-- Prove2me | solution 1 for P2M_allB_succ__7fe096bf361f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:52:15.811165+00:00
-- url     : https://prove2.me/submissions/9410f7fa-158e-415b-9b0e-6c860a84208f

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_FourThree_Theory
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ



set_option autoImplicit true
open Finset
theorem _root_.solution (A B c : ℕ) (hc : c.succ.ble (A.add B)) (ha : allA A B c)
    (hB : allB B c) :
    allB B.succ c := by
  simp only [Nat.add_eq, Nat.ble_eq] at hc
  intro b hbB hbc
  obtain hbB | rfl : b < B ∨ b = B := by grind
  · exact hB _ hbB hbc
  · rintro a ha0 hab - habc hgcd
    exact ha a ha0 hab (by lia) habc hgcd
