-- Prove2me | solution 1 for allA_succ_of_gcd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:52:22.316909+00:00
-- url     : https://prove2.me/submissions/ae050339-1f2f-4fa8-a3d4-c66949b53035

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
theorem _root_.solution (A b c g ga gb gc : ℕ) (hga : A.beq (ga.mul g)) (hgb : b.beq (gb.mul g))
    (hg : Nat.ble (nat_lit 2) g)
    (hgc : c.beq (gc.mul g)) (hA : allA A b c) :
    allA A.succ b c := by
  simp only [Nat.mul_eq, Nat.beq_eq, Nat.ble_eq] at hga hgb hgc hg
  subst hga hgb hgc
  apply allA_succ _ _ _ _ hA
  right
  rw [Nat.gcd_mul_right, Nat.gcd_mul_right]
  intro h
  have := Nat.eq_one_of_mul_eq_one_left h
  grind
