-- Prove2me | solution 1 for UlmsTheorem.exists_ulmHeight_eq_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:55:25.972808+00:00
-- url     : https://prove2.me/submissions/b3a5a713-0125-4598-b26a-f8553d753938

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_limit_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero



set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ)
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
namespace UlmsTheorem
theorem _root_.solution
    (hG : IsPReduced p G) {x : G} (hx0 : x ≠ 0) :
    ∃ α : Ordinal.{0},
      x ∈ ulmSubgroup p α (G := G) ∧
      x ∉ ulmSubgroup p (Order.succ α) (G := G) := by
  obtain ⟨γ, hγ⟩ := hG
  have hxγ : x ∉ ulmSubgroup p γ (G := G) := by
    rw [hγ]
    simpa using hx0
  obtain ⟨δ, hδmin⟩ :=
    exists_minimal_of_wellFoundedLT
      (fun β : Ordinal.{0} ↦ x ∉ ulmSubgroup p β (G := G)) ⟨γ, hxγ⟩
  rcases Ordinal.zero_or_succ_or_isSuccLimit δ with hδ0 | ⟨α, rfl⟩ | hδlim
  · subst δ
    exact False.elim (hδmin.1 (by simp))
  · refine ⟨α, ?_, hδmin.1⟩
    by_contra hxα
    exact hδmin.not_prop_of_lt (Order.lt_succ α) hxα
  · have hnotall :
        ¬ ∀ β < δ, x ∈ ulmSubgroup p β (G := G) := by
      simpa [mem_ulmSubgroup_limit_iff p hδlim x] using hδmin.1
    push Not at hnotall
    obtain ⟨β, hβδ, hxβ⟩ := hnotall
    exact False.elim (hδmin.not_prop_of_lt hβδ hxβ)
end UlmsTheorem
