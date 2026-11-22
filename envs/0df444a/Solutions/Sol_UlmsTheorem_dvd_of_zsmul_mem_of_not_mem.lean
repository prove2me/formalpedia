-- Prove2me | solution 1 for UlmsTheorem.dvd_of_zsmul_mem_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:57:32.103883+00:00
-- url     : https://prove2.me/submissions/57fc9a0b-74ad-4f8a-af59-fdd926b3ad00

module
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.pOrder_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero



set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
namespace UlmsTheorem
theorem _root_.solution
    {A : AddSubgroup G} {g : G}
    (hg_notin : g ∉ A) (hpg_in : p • g ∈ A)
    (k : ℤ) (hk : k • g ∈ A) : (↑p : ℤ) ∣ k := by
  let qg : G ⧸ A := QuotientAddGroup.mk g
  have hkq : k • qg = 0 := by
    change QuotientAddGroup.mk (k • g) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact hk
  have hpq : p • qg = 0 := by
    change QuotientAddGroup.mk (p • g) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact hpg_in
  have hq_ne : qg ≠ 0 := by
    intro hq
    apply hg_notin
    rw [QuotientAddGroup.eq_zero_iff] at hq
    exact hq
  have horder_dvd : addOrderOf qg ∣ p := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    simpa using hpq
  have horder_eq : addOrderOf qg = p := by
    rw [Nat.dvd_prime hp.1] at horder_dvd
    rcases horder_dvd with horder_one | horder_eq
    · exfalso
      apply hq_ne
      have hzero : (1 : ℕ) • qg = 0 := by
        rw [← horder_one]
        exact addOrderOf_nsmul_eq_zero qg
      simpa using hzero
    · exact horder_eq
  exact horder_eq ▸ addOrderOf_dvd_iff_zsmul_eq_zero.mpr hkq
end UlmsTheorem
