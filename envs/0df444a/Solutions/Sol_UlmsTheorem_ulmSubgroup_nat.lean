-- Prove2me | solution 1 for UlmsTheorem.ulmSubgroup_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:54:47.284768+00:00
-- url     : https://prove2.me/submissions/397bc583-827d-4d6b-91e6-470823f96212

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_add_one
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_pImage_pPow
public import Theorems.Thm_UlmsTheorem_pPow_zero_eq
attribute [local simp] UlmsTheorem.mem_pImage


attribute [local simp] UlmsTheorem.ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution (n : ℕ) : ulmSubgroup p (n : Ordinal) (G := G) = pPow p n := by
  induction n with
  | zero =>
      rw [show ((0 : ℕ) : Ordinal) = 0 by simp, ulmSubgroup_zero, pPow_zero_eq]
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : Ordinal) = (n : Ordinal) + 1 by simp]
      rw [ulmSubgroup_add_one, ih, pImage_pPow]
end UlmsTheorem
