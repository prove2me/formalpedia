-- Prove2me | solution 1 for accept_of_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:52:37.730046+00:00
-- url     : https://prove2.me/submissions/bf42142c-e101-44fd-81b1-f7aa83968a3f

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
import Theorems.Thm_le_polychromNumber_iff_hasPolychromColouring
import Theorems.Thm_polychromNumber_image
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
theorem _root_.solution {a b c : ℕ}
    (h : ({0, 1, 2} : Finset (ZMod 3)) ⊆ {0, (a : ZMod 3), (b : ZMod 3), (c : ZMod 3)}) :
    Accept a b c := by
  rw [Accept, ← le_polychromNumber_iff_hasPolychromColouring (by simp)]
  grw [← polychromNumber_image (Int.castAddHom (ZMod 3))]
  simp only [Int.coe_castAddHom, image_insert, Int.cast_zero, Int.cast_natCast, image_singleton]
  change univ ⊆ _ at h
  simp only [univ_subset_iff] at h
  simp [h]
