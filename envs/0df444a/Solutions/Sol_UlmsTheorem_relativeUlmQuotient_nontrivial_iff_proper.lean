-- Prove2me | solution 1 for UlmsTheorem.relativeUlmQuotient_nontrivial_iff_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:27.190586+00:00
-- url     : https://prove2.me/submissions/32d5faaa-d666-4a95-86cd-b97d37a78c17

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
public import Theorems.Thm_UlmsTheorem_isProper_iff_forall_not_mem_succ
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_ulmHeight_le_of_mem_imp
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_antitone
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
    (S : AddSubgroup G) (α : Ordinal.{0}) :
    Nontrivial (relativeUlmQuotient p S α) ↔
      ∃ v : G, v ∈ pSocleAt p α (G := G) ∧
        v ∉ ulmSubgroup p (Order.succ α) (G := G) ∧
        IsProper p S v := by
  constructor
  · intro hroom
    rw [Submodule.Quotient.nontrivial_iff] at hroom
    obtain ⟨v, _, hv⟩ :=
      SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hroom)
    have hv' : (v : G) ∉
        pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α)) := by
      exact hv
    have hvSucc : (v : G) ∉ ulmSubgroup p (Order.succ α) := by
      intro hvs
      exact hv' ⟨v.property, AddSubgroup.mem_sup_right hvs⟩
    refine ⟨v, v.property, hvSucc, ?_⟩
    intro s
    apply ulmHeight_le_of_mem_imp p ((v : G) + s) v
    intro β hvsum
    by_cases hβα : β ≤ α
    · exact ulmSubgroup_antitone p hβα v.property.2
    · have hsucc : Order.succ α ≤ β :=
        Order.succ_le_iff.mpr (lt_of_not_ge hβα)
      have hvsumSucc :
          (v : G) + s ∈ ulmSubgroup p (Order.succ α) :=
        ulmSubgroup_antitone p hsucc hvsum
      exfalso
      apply hv'
      refine ⟨v.property, ?_⟩
      have heq : (v : G) = (-s : G) + ((v : G) + s) := by
        abel
      rw [heq]
      exact AddSubgroup.add_mem_sup (S.neg_mem s.property) hvsumSucc
  · rintro ⟨v, hvP, hvSucc, hvProper⟩
    rw [Submodule.Quotient.nontrivial_iff]
    intro htop
    let vP : pSocleAt p α (G := G) := ⟨v, hvP⟩
    have hvden : vP ∈ relativeUlmSubmodule p S α := by
      change vP ∈ hillSubmodule p S α
      rw [htop]
      trivial
    change v ∈ pSocleAt p α ⊓
      (S ⊔ ulmSubgroup p (Order.succ α)) at hvden
    obtain ⟨s, hs, g, hg, hsg⟩ := AddSubgroup.mem_sup.mp hvden.2
    have heq : v + -s = g := by
      rw [← hsg]
      abel
    exact (isProper_iff_forall_not_mem_succ p S hvP.2 hvSucc).1 hvProper
      ⟨-s, S.neg_mem hs⟩ (by simpa [heq] using hg)
end UlmsTheorem
