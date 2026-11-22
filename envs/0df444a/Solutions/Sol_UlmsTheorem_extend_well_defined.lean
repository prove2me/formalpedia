-- Prove2me | solution 1 for UlmsTheorem.extend_well_defined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:54.027859+00:00
-- url     : https://prove2.me/submissions/c831cf9f-bf5c-463e-a584-89a339d4db28

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
public import Theorems.Thm_UlmsTheorem_phi_zsmul_eq_zsmul_h
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
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B)
    {g : G} (hg_notin : g ∉ A) (hpg_in : p • g ∈ A)
    {h : H} (hh_eq : p • h = (↑(φ ⟨p • g, hpg_in⟩) : H))
    {a₁ a₂ : G} {n₁ n₂ : ℤ} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (heq : a₁ + n₁ • g = a₂ + n₂ • g) :
    (↑(φ ⟨a₁, ha₁⟩) : H) + n₁ • h = (↑(φ ⟨a₂, ha₂⟩) : H) + n₂ • h := by
  have hrepr' : a₁ - a₂ = n₂ • g - n₁ • g := by
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm, add_left_comm, add_assoc] using heq)
  have hrepr : a₁ - a₂ = (n₂ - n₁) • g := by
    simpa [sub_eq_add_neg, add_zsmul] using hrepr'
  have hkg : (n₂ - n₁) • g ∈ A := by
    rw [← hrepr]
    exact A.sub_mem ha₁ ha₂
  have hphi :
      (φ ⟨(n₂ - n₁) • g, hkg⟩ : H) = (n₂ - n₁) • h := by
    exact phi_zsmul_eq_zsmul_h (p := p) φ hg_notin hpg_in hh_eq (n₂ - n₁) hkg
  have hsub :
      (φ ⟨a₁ - a₂, A.sub_mem ha₁ ha₂⟩ : H) = (n₂ - n₁) • h := by
    have hsame :
        (⟨a₁ - a₂, A.sub_mem ha₁ ha₂⟩ : A) = ⟨(n₂ - n₁) • g, hkg⟩ := by
      apply Subtype.ext
      exact hrepr
    simpa [hsame] using hphi
  have hmap_sub :
      (φ ⟨a₁ - a₂, A.sub_mem ha₁ ha₂⟩ : H) =
        (φ ⟨a₁, ha₁⟩ : H) - (φ ⟨a₂, ha₂⟩ : H) := by
    exact congrArg (fun z : B ↦ (z : H)) (φ.map_sub ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩)
  have hdiff :
      (φ ⟨a₁, ha₁⟩ : H) - (φ ⟨a₂, ha₂⟩ : H) = (n₂ - n₁) • h := by
    exact hmap_sub.symm.trans hsub
  have hsum :
      (φ ⟨a₁, ha₁⟩ : H) = (n₂ - n₁) • h + (φ ⟨a₂, ha₂⟩ : H) := by
    rwa [sub_eq_iff_eq_add] at hdiff
  calc
    (↑(φ ⟨a₁, ha₁⟩) : H) + n₁ • h = ((n₂ - n₁) • h + (φ ⟨a₂, ha₂⟩ : H)) + n₁ • h := by
      rw [hsum]
    _ = (↑(φ ⟨a₂, ha₂⟩) : H) + ((n₂ - n₁) • h + n₁ • h) := by
      abel
    _ = (↑(φ ⟨a₂, ha₂⟩) : H) + ((n₂ - n₁ + n₁) • h) := by
      rw [← add_zsmul]
    _ = (↑(φ ⟨a₂, ha₂⟩) : H) + n₂ • h := by
      congr 1
      abel_nf
end UlmsTheorem
