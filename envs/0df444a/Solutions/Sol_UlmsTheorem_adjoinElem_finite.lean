-- Prove2me | solution 1 for UlmsTheorem.adjoinElem_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:02.661627+00:00
-- url     : https://prove2.me/submissions/1e633506-1b33-4715-b849-5b769255be49

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
public import Theorems.Thm_UlmsTheorem_adjoinElem_fg
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
    (hG : IsPrimaryPGroup p G)
    {A : AddSubgroup G} (hAfinite : Set.Finite (A : Set G)) (g : G) :
    Set.Finite (adjoinElem A g : Set G) := by
  have hAfg : A.FG :=
    (AddSubgroup.fg_iff A).2 ⟨(A : Set G), by simp, hAfinite⟩
  have hadjfg : (adjoinElem A g).FG := adjoinElem_fg hAfg g
  let _ : AddGroup.FG (adjoinElem A g) :=
    (AddGroup.fg_iff_addSubgroup_fg (adjoinElem A g)).2 hadjfg
  have htors : IsAddTorsion (adjoinElem A g) := by
    intro z
    obtain ⟨n, hn⟩ := hG (z : G)
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨p ^ n, pow_pos hp.out.pos n, ?_⟩
    apply Subtype.ext
    exact hn
  let _ : Finite (adjoinElem A g) :=
    AddCommGroup.finite_of_fg_isAddTorsion (adjoinElem A g) htors
  have hrange :
      Set.range (fun z : adjoinElem A g ↦ (z : G)) =
        (adjoinElem A g : Set G) := by
    ext z
    simp
  rw [← hrange]
  exact Set.finite_range _
end UlmsTheorem
