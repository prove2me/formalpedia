-- Prove2me | solution 1 for UlmsTheorem.extend_by_one_fg_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:53.53122+00:00
-- url     : https://prove2.me/submissions/1956f57f-803a-445f-bafe-69ceb778f3cd

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

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
omit hp
namespace UlmsTheorem
theorem _root_.solution
    {A : AddSubgroup G} (hA : IsPure p A) (hAfg : A.FG)
    {B : AddSubgroup H} (hB : IsPure p B) (hBfg : B.FG)
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    {g : G} (hg : g ∈ A) :
    ∃ (A' : AddSubgroup G) (_ : IsPure p A') (_ : A'.FG) (hAA' : A ≤ A') (_ : g ∈ A')
      (B' : AddSubgroup H) (_ : IsPure p B') (_ : B'.FG) (_ : B ≤ B')
      (φ' : A' →+ B'),
        IsHeightPresOn p φ' ∧
        ∀ a : A, (φ' ⟨a, hAA' a.prop⟩ : H) = φ a := by
  refine ⟨A, hA, hAfg, le_rfl, hg, B, hB, hBfg, le_rfl, φ, hφ, ?_⟩
  intro a
  rfl
end UlmsTheorem
