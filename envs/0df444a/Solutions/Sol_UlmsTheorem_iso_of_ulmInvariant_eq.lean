-- Prove2me | solution 1 for UlmsTheorem.iso_of_ulmInvariant_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:04:44.98125+00:00
-- url     : https://prove2.me/submissions/1b25d1df-b5ac-4770-a7f3-22e27f6061db

module
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Classification
public import Theorems.Thm_UlmsTheorem_iso_of_ulmInvariant_eq_of_backAndForth
public import Theorems.Thm_UlmsTheorem_kaplansky_extend
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


section
@[expose] public section
namespace UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
private lemma kaplansky_extend_back
    (hH : IsReducedPGroup p H)
    (hinv : ∀ β : Ordinal.{0},
      ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    (s : BFIsoStep p (G := G) (H := H)) (h : H) :
    ∃ (s' : BFIsoStep p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      h ∈ s'.B ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by
  obtain ⟨t, hBB, hAA, hh, hcomp⟩ :=
    kaplansky_extend (p := p) hH (fun β ↦ (hinv β).symm) s.symm h
  refine ⟨t.symm, hAA, hBB, hh, ?_⟩
  intro a
  have ht :
      t.e ⟨s.e a, hBB (s.e a).prop⟩ = ⟨a, hAA a.prop⟩ := by
    apply Subtype.ext
    have hc := hcomp (s.e a)
    change (t.e ⟨s.e a, hBB (s.e a).prop⟩ : G) =
      (s.e.symm (s.e a) : G) at hc
    exact hc.trans (congrArg Subtype.val (s.e.symm_apply_apply a))
  have hsymm := congrArg t.e.symm ht
  have hvals :
      (s.e a : H) = (t.e.symm ⟨a, hAA a.prop⟩ : H) := by
    simpa using congrArg Subtype.val hsymm
  exact hvals.symm
end UlmsTheorem
end
end

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
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G)
    (hH : IsReducedPGroup p H)
    (hinv : ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H)) :
    Nonempty (G ≃+ H) := by
  apply iso_of_ulmInvariant_eq_of_backAndForth (p := p)
  · exact fun s g ↦ kaplansky_extend (p := p) hG hinv s g
  · exact fun s h ↦ kaplansky_extend_back (p := p) hH hinv s h
end UlmsTheorem
