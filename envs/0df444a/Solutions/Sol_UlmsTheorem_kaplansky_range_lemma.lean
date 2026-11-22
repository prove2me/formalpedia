-- Prove2me | solution 1 for UlmsTheorem.kaplansky_range_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:00:04.976682+00:00
-- url     : https://prove2.me/submissions/0ffb3237-4168-43ee-9e2c-bd9e79944cb1

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
public import Theorems.Thm_UlmsTheorem_kaplanskyMap_injective
public import Theorems.Thm_UlmsTheorem_kaplanskyMap_not_surjective_iff_proper

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
theorem _root_.solution (S : AddSubgroup G) (α : Ordinal.{0}) :
    ∃ U : kaplanskyDomainQuotient p S α →+
        ulmQuotient p α (G := G),
      Function.Injective U ∧
      (¬ Function.Surjective U ↔
        ∃ v : G, v ∈ pSocleAt p α (G := G) ∧
          v ∉ ulmSubgroup p (Order.succ α) (G := G) ∧
          IsProper p S v) := by
  exact ⟨kaplanskyMap p S α, kaplanskyMap_injective p S α,
    kaplanskyMap_not_surjective_iff_proper p S α⟩
end UlmsTheorem
