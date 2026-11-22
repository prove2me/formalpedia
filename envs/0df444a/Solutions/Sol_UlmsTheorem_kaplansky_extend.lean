-- Prove2me | solution 1 for UlmsTheorem.kaplansky_extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:04:01.225713+00:00
-- url     : https://prove2.me/submissions/7fecb322-4935-48a9-a166-0f3b6ee2f260

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
public import Theorems.Thm_UlmsTheorem_kaplansky_extend_one
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
    (hG : IsReducedPGroup p G)
    (hinv : ∀ β : Ordinal.{0},
      ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    (s : UlmStage p (G := G) (H := H)) (g : G) :
    ∃ (s' : UlmStage p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      g ∈ s'.A ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by
  have extend_pow :
      ∀ n : ℕ, ∀ t : UlmStage p (G := G) (H := H),
        p ^ n • g ∈ t.A →
        ∃ (t' : UlmStage p (G := G) (H := H))
          (hAA : t.A ≤ t'.A) (_hBB : t.B ≤ t'.B),
          g ∈ t'.A ∧
          ∀ a : t.A, (t'.e ⟨a, hAA a.prop⟩ : H) = t.e a := by
    intro n
    induction n with
    | zero =>
        intro t hpow
        have hgA : g ∈ t.A := by simpa using hpow
        exact ⟨t, le_rfl, le_rfl, hgA, fun _ ↦ rfl⟩
    | succ n ih =>
        intro t hpow
        let y : G := p ^ n • g
        have hpyA : p • y ∈ t.A := by
          simpa [y, pow_succ, mul_smul, Nat.mul_comm] using hpow
        obtain ⟨t₁, hAA₁, hBB₁, hy₁, hext₁⟩ :=
          kaplansky_extend_one p hG hinv t y hpyA
        obtain ⟨t₂, hAA₂, hBB₂, hg₂, hext₂⟩ :=
          ih t₁ hy₁
        let hAA : t.A ≤ t₂.A := hAA₁.trans hAA₂
        let hBB : t.B ≤ t₂.B := hBB₁.trans hBB₂
        refine ⟨t₂, hAA, hBB, hg₂, ?_⟩
        intro a
        calc
          (t₂.e ⟨a, hAA a.prop⟩ : H) =
              t₁.e ⟨a, hAA₁ a.prop⟩ := hext₂ ⟨a, hAA₁ a.prop⟩
          _ = t.e a := hext₁ a
  obtain ⟨n, hn⟩ := hG.primary g
  exact extend_pow n s (by simp [hn])
end UlmsTheorem
